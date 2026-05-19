{-|
Module      : SymExec
Description : Symbolic execution engine
Copyright   : (c) Matthew Amy, 2026
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Frontend.OpenQASM3.SymExec where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
  
import Data.Functor.Identity (Identity)

import Data.Complex
import Data.Maybe (fromJust)
import Data.Bits
import Data.List

import Control.Monad.State.Strict hiding (lift)

import Feynman.Core (ID, discretize, Angle(..))
import Feynman.Algebra.Base
import Feynman.Algebra.Pathsum.Balanced
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Algebra.SArith2

import Feynman.Frontend.OpenQASM3.Core
import Feynman.Frontend.OpenQASM3.TypeCheck hiding (Env, isConstant, openProcScope, initEnv)

import qualified Feynman.Util.Unicode as U

{- Notes

  1. Eval in Lvalue context to locations, every other context follow to a value
  2. Give instances for Num and Bits on SI, SUI, SB
  3. That would allow us to allocate uint types on the heap as well
  4. Could short cut the refactor by replacing Vpolylist with SInt
-}

{-----------------------------
 Data types
 -----------------------------}

-- | Monadic interface for symbolic executions
type SymExecM m = StateT SimEnv m

-- | Basic simulator type
type Simulator = SymExecM Identity

-- | Environment type
type Env = Map ID Value

-- | Execution environment
data SimEnv = SimEnv {
  pathsum :: Pathsum DMod2,
  globals :: Env,
  locals  :: [Env],
  qwidth  :: Int -- number of allocated qubits
} deriving (Show)

-- | Types which have a symbolic component
data SimInteger  = KnownI Integer  | SymbolicI    (SInt Var)  deriving (Show)
data SimUInteger = KnownUI Integer | SymbolicUI   (SUInt Var) deriving (Show)
data SimBool     = KnownB Bool     | SymbolicB (SBool Var) deriving (Show)

class SymbolicRepr a where
  type C
  type S
  toSymbolic :: C -> S
  packUnary :: (C -> C) (S -> S) -> a -> a
  packBinary :: (C -> C -> C) (S -> S -> S) -> a -> a -> a

instance SymbolicRepr SimInteger where
  type C = Integer
  type S = SInt Var
  toSymbolic = makeSymbolic

instance SymbolicRepr SimUInteger where
  type C = Integer
  type S = SUInt Var
  toSymbolic = makeSymbolic

instance SymbolicRepr SimBool where
  type C = Bool
  type S = SBool Var
  toSymbolic b = if b then 1 else 0

-- | Values of the simulator
data Value =
    VUnit
  | VUndefined
  | VLoc Integer
  | VLocList [Integer]
  | VInt SimInteger
  | VUInt SimUInteger
  | VBool SimBool
  | VList [Value]
  | VFloat Double
  | VCmplx (Complex Double)
  | VProc { params :: [(ID, Type)],
            returns :: Maybe Type,
            body :: Stmt ElaboratedType,
            summary :: Maybe (Pathsum DMod2) }
  deriving (Show)

-- | LValues for assignment
data LValue = LID ID | LLoc Integer | LLocList [Integer] deriving (Show)

{-----------------------------
 Data utilities
 -----------------------------}

-- | Attempts to concretize an integer
toKnownInt :: SimInteger -> Maybe Integer
toKnownInt (KnownI i)    = Just i
toKnownInt (SymbolicI i) = fromSymbolic i

-- | Attempts to concretize an unsigned integer
toKnownUInt :: SimUInteger -> Maybe Integer
toKnownUInt (KnownUI i)    = Just i
toKnownUInt (SymbolicUI i) = fromSymbolic i

-- | Attempts to concretize a Boolean
toKnownBool :: SimBool -> Maybe Bool
toKnownBool (KnownB b)    = Just b
toKnownBool (SymbolicB b) = case isConstant b of
  True  -> Just $ 1 == getConstant b
  False -> Nothing

-- | Utility for casting symbolic values
castS :: Maybe a -> a
castS Nothing  = error "Runtime conversion from symbolic to non-symbolic value"
castS (Just a) = a

-- | Indexes a value
indexVal :: Value -> Value -> Value
indexVal val idx = case (val, resolve idx) of
    (VLocList xs, Left j)   -> VLoc $ xs!!j
    (VLocList xs, Right js) -> VLocList $ [xs!!j | j <- js]
    (VInt si, Left j)       -> case si of
      KnownI i    -> VUInt . KnownUI $ if testBit i j then 1 else 0
      SymbolicI i -> VUInt . SymbolicUI . SBits $ [testBitS i j]
    (VInt si, Right js)     -> case si of
      KnownI i    -> VUInt . KnownUI $ fromBits [if testBit i j then 1 else 0 | j <- js]
      SymbolicI i -> VUInt . SymbolicUI . SBits $ [testBitS i j | j <- js]
    (VUInt si, Left j)      -> case si of
      KnownUI i    -> VUInt . KnownUI $ if testBit i j then 1 else 0
      SymbolicUI i -> VUInt . SymbolicUI . SBits $ [testBitS i j]
    (VUInt si, Right js)    -> case si of
      KnownUI i    -> VUInt . KnownUI $ fromBits [if testBit i j then 1 else 0 | j <- js]
      SymbolicUI i -> VUInt . SymbolicUI . SBits $ [testBitS i j | j <- js]
    _                       -> error "non indexable expression"
  where resolve idx = case idx of
          VList ids -> Right $ map resolveInt ids
          _         -> Left $ resolveInt idx
        fromBits    = foldr (+) 0 . map foo . zip [0..]
        foo (i,b)   = b `shiftL` i

-- | Resolves a value to a (non-symbolic) integer
resolveInt :: Value -> Int
resolveInt val = case val of
  VInt si  -> fromIntegral $ castS $ toKnownInt si
  VUInt si -> fromIntegral $ castS $ toKnownUInt si
  VBool sb -> if (castS $ toKnownBool sb) then 1 else 0
  _        -> error "Unexpected non-integral expression"

-- | Resolves an l-value to a location
resolveLoc :: LValue -> Integer
resolveLoc lval = case lval of
  LLoc i -> fromIntegral i
  _      -> error "Unexpected lvalue expression"

{-----------------------------
 Environmental utilities
 -----------------------------}

-- | Initial environment
initEnv :: SimEnv
initEnv = SimEnv (ket []) Map.empty [Map.empty] 0

-- | Opens a new local scope
openScope :: Simulator ()
openScope = modify $ \env -> env { locals = Map.empty : locals env }

-- | Closes the current local scope
closeScope :: Simulator ()
closeScope = modify $ \env -> env { locals = tail $ locals env }

-- | Opens a new procedure scope
openProcScope :: Simulator [Env]
openProcScope = do
  env <- get
  put $ env { locals = Map.empty : locals env }
  return $ locals env

-- | Restores the local scope after a procedure
restoreScope :: [Env] -> Simulator ()
restoreScope e = modify $ \env -> env { locals = e }

-- | Adds a binding to the environment
declare :: Bool -> ID -> Value -> Simulator ()
declare isGlobal id val = case isGlobal of
  True ->  modify $ \env -> env { globals = Map.insert id val (globals env) }
  False -> do
    env <- get
    let (b:bs) = locals env
    put $ env { locals = (Map.insert id val b) : bs }

-- | Binds parameters of a function
declareParams :: [(ID, Type)] -> [Value] -> Simulator ()
declareParams params args = mapM_ go $ zip params args where
  go ((id,_), val) = declare False id val
    
-- | Finds a binding in the environment
searchBinding :: ID -> Simulator Value
searchBinding id = do
  res <- gets $ \env -> msum . map (Map.lookup id) $ (globals env : locals env)
  case res of
    Nothing -> error $ "Fatal: no binding found for " ++ show id
    Just v  -> return v

{-----------------------------
 Heap-specific
 -----------------------------}

-- | Allocates a new variable
allocVar :: ID -> Type -> Simulator Value
allocVar id typ = case typ of
  TBool         -> return VUndefined
  TCReg l       -> do
    id <- freshen id
    allocHeap False id l
  TQBit         -> do
    id <- freshen id
    ~(VLocList [x]) <- allocHeap True id 1
    return $ VLoc x
  TQReg l       -> do
    id <- freshen id
    allocHeap True id l
  TUInt Nothing -> return VUndefined
  TUInt (Just l)-> do
    id <- freshen id
    return $ VUInt $ SymbolicUI $ SBits [ofVar (FVar $ fvar id i) | i <- [0..l-1]]
  TInt Nothing  -> return VUndefined
  TInt (Just l) -> do
    id <- freshen id
    return $ VInt $ SymbolicI $ SBits [ofVar (FVar $ fvar id i) | i <- [0..l-1]]
  TAngle _      -> return VUndefined
  TFloat _      -> return VUndefined
  TCmplx _      -> return VUndefined

-- | Allocates space on the heap
allocHeap :: Bool -> ID -> Integer -> Simulator Value
allocHeap False pref size = do
  env <- get
  let offset = outDeg $ pathsum env
  let st     = ket $ [ofVar (fvar pref i) | i <- [0..size-1]]
  let ps'    = pathsum env .> embed st offset (\i -> i) (\i -> i + offset)
  put $ env { pathsum = ps' }
  return $ VLocList [i + (toInteger offset) | i <- [0..size-1]]
allocHeap True pref size = do
  env <- get
  let offset = qwidth env
  let st  = ket $ [ofVar (fvar pref i) | i <- [0..size-1]] ++
                  [ofVar (fvar (pref ++ "'") i) | i <- [0..size-1]]
  let ps' =
        let idx i = if i < (fromIntegral size) then i + offset else i + 2*offset in
          pathsum env .> embed st (outDeg $ pathsum env) (\i -> i) idx
  put $ env { pathsum = ps', qwidth = offset + (fromIntegral size) }
  return $ VLocList [i + (toInteger offset) | i <- [0..size-1]]

-- | Allocates space on the heap
allocWith :: Bool -> [SBool String] -> Simulator Value
allocWith b xs = do
  env <- get
  let size   = if b then (length xs) `div` 2 else length xs
  let offset = if b then qwidth env else (outDeg $ pathsum env)
  let outI i = if b then
                 (if i < size then i + offset else i + 2*offset)
               else
                 i + offset
  let ps' = pathsum env .> embed (ket xs) (outDeg $ pathsum env) (\i -> i) outI
  put $ env { pathsum = ps' }
  return $ VLocList [toInteger (i + offset) | i <- [0..size-1]]

-- | Freshens a variable identifier
freshen :: ID -> Simulator ID
freshen vid = do
  fvars <- gets (Set.fromList . map removeSubs . freeVars . pathsum)
  return . fromJust . find (`Set.notMember` fvars) $ (vid:[vid ++ (show i) | i <- [1..]])
  where removeSubs = takeWhile (`notElem` subscripts)
        subscripts = concat [U.subscript i | i <- [0..9]]

-- | Looks up the value at a particular location in memory
lookupLoc :: Integer -> Simulator (SBool Var)
lookupLoc i = gets $ (!!(fromIntegral i)) . outVals . pathsum

{-
-- | Dereferences a value
deref :: Value -> Integer -> Value
deref v idx = case v of

  VInt i          -> VBool $ ((i `shiftR` (fromInteger idx)) `mod` 2) == 1

  VQReg start len -> if idx < len then
                       VQBit (start + idx)
                     else
                       error "Out of bounds array access"

  VCReg start len -> if idx < len then
                       VCBit (start + idx)
                     else
                       error "Out of bounds array access"

  VPolyList xs    -> if idx < toInteger (length xs) then
                       VPoly (xs!!(fromInteger idx))
                     else
                       error "Out of bounds array access"

  _               -> error "Unexpected: value is not indexable"

-- | Assigns a scalar to a new value. Note that only locals can be modified
assignScalar :: ID -> Type -> Value -> Simulator ()
assignScalar id ty v = modify $ \env -> env { locals = assign (locals env) } where
  assign []     = error $ "No binding for variable " ++ show id
  assign (c:cs) = case Map.lookup id c of
    Just _ -> (Map.insert id (Scalar ty v) c):cs
    _      -> c:(assign cs)

-- | Assigns a symbolic (classical) variable to a new value
assignSymbolic :: SBool Var -> Type -> Integer -> Value -> Simulator ()
assignSymbolic p ty offset v = case (ty, v) of
  (_, VBool b)    -> modify $ write [0]
  (_, VPoly poly) -> modify $ write [poly]
  (TCReg n, _)    -> modify $ write (castSymbolic n v)
  (TUInt n, _)    -> modify $ write (castSymbolic n v)
  _               -> error $ "Type " ++ show ty ++ " is not a symbolic type"
  where

    castSymbolic n v = case v of
      VBool b -> makeSNat (if b then 1 else 0)
      VInt i  -> makeSNat (toInteger i)

    write xs env =
      let idx = fromInteger offset
          ps = applyPControlled (overwrite xs) p [idx..idx+length xs] $ pathsum env
      in
        env { pathsum = ps }
-}

-- | Gives the unicode representation of the ith offset of v
fvar :: ID -> Integer -> String
fvar v i = U.sub v i

-- | Retrieves the number of qubits on the heap
getQWidth :: Simulator Int
getQWidth = gets qwidth

-- | Retrieves the number of classical bits on the heap
getCWidth :: Simulator Int
getCWidth = gets $ \env -> outDeg (pathsum env) - 2*(qwidth env)

-- | Index of pathsum where classical registers start
getCOffset :: Simulator Int
getCOffset = gets $ \env -> 2*(qwidth env)

{-
-- | Returns the memory locations of a quantum variable
getQVarOffsets :: Value -> Simulator (Maybe [Int])
getQVarOffsets v = case v of
  VQBit i   -> return $ Just [fromInteger i]
  VQReg i j -> return $ Just [fromInteger i..fromInteger i+fromInteger j-1]
  _         -> return Nothing

-- | Returns the memory locations of a classical variable
getCVarOffsets :: Value -> Simulator (Maybe [Int])
getCVarOffsets v = do
  o <- getCOffset
  case v of
    VCBit i   -> return $ Just [fromInteger i+o]
    VCReg i j -> return $ Just [fromInteger i+o..fromInteger i+o+fromInteger j-1]
    _         -> return Nothing
-}

{-----------------------------
 Path sum utilities
 -----------------------------}

-- | Standard library
stdlib :: Map ID ([Value] -> Pathsum DMod2)
stdlib = Map.fromList $
  [("x", \_ -> xgate),
   ("y", \_ -> ygate),
   ("z", \_ -> zgate),
   ("h", \_ -> hgate),
   ("cx", \_ -> cxgate),
   ("cy", \_ -> (identity 1 <> sgate .> cxgate .> identity 1 <> sdggate)),
   ("cz", \_ -> czgate),
   ("ch", \_ -> chgate),
   ("id", \_ -> identity 1),
   ("s", \_ -> sgate),
   ("sdg", \_ -> sdggate),
   ("t", \_ -> tgate),
   ("tdg", \_ -> tdggate),
   ("ccx", \_ -> ccxgate),
   ("swap", \_ -> swapgate),
   ("gphase", \[o] -> gPhase (evalAngle o)),
   ("rz", \[o] -> rzgate (evalAngle o)),
   ("rx", \[o] -> hgate .> rzgate (evalAngle o) .> hgate),
   ("ry", \[o] -> sgate .> hgate .> rzgate (evalAngle o) .> hgate .> sdggate),
   ("crz", \[o] -> controlled $ rzgate (evalAngle o)),
   ("u3", \_ -> error "u3 gate not supported"),
   ("u2", \_ -> error "u2 gate not supported"),
   ("u1", \_ -> error "u1 gate not supported"),
   ("cu1", \_ -> error "cu1 gate not supported"),
   ("cu3", \_ -> error "cu3 gate not supported")]
  where evalAngle o = case o of
          VInt i -> fromDyadic . discretize . Continuous $ fromInteger 1
          VFloat d -> fromDyadic . discretize . Continuous $ d
          _ -> error "Invalid angle"

-- | Resets a qubit
resetQ :: SBool Var -> Integer -> Simulator ()
resetQ p i = modify $ \env -> env { pathsum = reset (qwidth env) (pathsum env) }
  where reset n = applyPControlled resetGate p [fromInteger i, fromInteger i + n - 1]

-- | Measures a qubit and return the (symbolic) result
measureQ :: SBool Var -> Integer -> Simulator (SBool Var)
measureQ p i = do
  modify $ \env -> env { pathsum = measure (qwidth env) (pathsum env) }
  gets $ \env -> (outVals $ pathsum env)!!(fromInteger i)
  where measure n = applyPControlled measureGate p [fromInteger i, fromInteger i + n - 1]

-- | Applies a path sum (e.g. a summary) to a list of parameters
applyBlock :: SBool Var -> [Integer] -> Pathsum DMod2 -> Simulator ()
applyBlock p offsets ps = modify $ \env -> env { pathsum = f (pathsum env) } where
  f = applyPControlled ps p (map fromIntegral offsets)

-- | Generates a path sum for a basic gate
generateGate :: ID -> [Value] -> Simulator (Pathsum DMod2)
generateGate id cargs = case Map.lookup id stdlib of
  Just ps -> return $ ps cargs
  Nothing -> do
    binding <- searchBinding id
    case binding of
      VProc _ _ _ (Just ps)         -> return ps
      VProc params ret body Nothing -> error "Unimplemented" -- do
        -- Generate a summary of the gate
        -- env <- get
        -- put $ env { pathsum = mempty, qwidth = 0, locals = [Map.empty] }
        -- bindParams (zip params (repeat (TAngle Nothing))) cargs
        
{-----------------------------
 Casting & data operations
 -----------------------------}

-- | Casts a value of one type as another type
castValue :: Type -> Value -> Simulator Value
castValue ty val = case ty of
  TBool -> case val of
    VBool _              -> return val
    VInt  (KnownI i)     -> return . VBool . KnownB $ i /= 0
    VInt  (SymbolicI i)  -> return . VBool . SymbolicB $ testBitS i 0
    VUInt (KnownUI i)    -> return . VBool . KnownB $ i /= 0
    VUInt (SymbolicUI i) -> return . VBool . SymbolicB $ testBitS i 0
    VFloat f             -> return . VBool . KnownB $ f /= 0.0
      
  TInt m -> case val of
    VBool (KnownB b)       -> return . VInt . KnownI $ if b then 1 else 0
    VBool (SymbolicB b)    -> return . VInt . SymbolicI $ setWidthM (SBits [b]) m
    VInt (KnownI i)        -> return . VInt . KnownI $ i
    VInt (SymbolicI i)     -> return . VInt . SymbolicI $ setWidthM (convertSign i) m
    VUInt (KnownUI i)      -> return . VInt . KnownI $ i
    VUInt (SymbolicUI i)   -> return . VInt . SymbolicI $ setWidthM (convertSign i) m
    VFloat f               -> return . VInt . KnownI . truncate $ f
    VLoc l                 -> do
      b <- lookupLoc l
      return . VInt . SymbolicI $ setWidthM (SBits [b]) m
    VLocList xs            -> do
      bs <- mapM lookupLoc xs
      return . VInt . SymbolicI $ setWidthM (SBits bs) m

  TUInt m -> case val of
    VBool (KnownB b)       -> return . VUInt . KnownUI $ if b then 1 else 0
    VBool (SymbolicB b)    -> return . VUInt . SymbolicUI $ setWidthM (SBits [b]) m
    VInt (KnownI i)        -> return . VUInt . KnownUI $ unsign i
    VInt (SymbolicI i)     -> return . VUInt . SymbolicUI $ setWidthM (convertSign i) m
    VUInt (KnownUI i)      -> return . VUInt . KnownUI $ i
    VUInt (SymbolicUI i)   -> return . VUInt . SymbolicUI $ setWidthM (convertSign i) m
    VFloat f               -> return . VUInt . KnownUI . unsign . truncate $ f
    VLoc l                 -> do
      b <- lookupLoc l
      return . VUInt . SymbolicUI $ setWidthM (SBits [b]) m
    VLocList xs            -> do
      bs <- mapM lookupLoc xs
      return . VUInt . SymbolicUI $ setWidthM (SBits bs) m

  TFloat _ -> case val of
    VInt si  -> return . VFloat . fromIntegral . castS . toKnownInt $ si
    VUInt si -> return . VFloat . fromIntegral . castS . toKnownUInt $ si
    VFloat f -> return val
    VBool sb -> return . VFloat . (\b -> if b then 1.0 else 0.0) . castS . toKnownBool $ sb

  TAngle _ -> case val of
    VFloat f  -> return . VFloat $ f / pi

  -- Allocate space in memory
  TCReg m -> case val of
    VInt  (KnownI i)     -> return . VBool . KnownB $ i /= 0
    VInt  (SymbolicI i)  -> return . VBool . SymbolicB $ testBitS i 0
    VUInt (KnownUI i)    -> return . VBool . KnownB $ i /= 0
    VUInt (SymbolicUI i) -> return . VBool . SymbolicB $ testBitS i 0
    VLocList ks          -> return val

  _ -> error "Runtime cast error"
  
  where unsign i = case i < 0 of
          True  -> error "Casting negative value to unsigned integer"
          False -> i
        setWidthM si Nothing  = si
        setWidthM si (Just m) = setWidth si (fromIntegral m)

{-----------------------------
 Simulation
 -----------------------------}

-- | Evaluates a type expression
evalType :: TypeExpr ElaboratedType -> Simulator Type
evalType typ = case typ of
  TQBit -> return TQBit
  TBool -> return TBool
  TUnit -> return TUnit

  TCReg e -> liftM TCReg $ evalToInt e
  TQReg e -> liftM TQReg $ evalToInt e

  TUInt me  -> liftM TUInt $ maybe (return Nothing) (liftM Just . evalToInt) me
  TInt me   -> liftM TInt $ maybe (return Nothing) (liftM Just . evalToInt) me
  TAngle me -> liftM TAngle $ maybe (return Nothing) (liftM Just . evalToInt) me
  TFloat me -> liftM TFloat $ maybe (return Nothing) (liftM Just . evalToInt) me
  TCmplx me -> liftM TCmplx $ maybe (return Nothing) (liftM Just . evalToInt) me

  TRange ts -> liftM TRange $ evalType ts

  TGate c q -> return $ TGate c q
  TProc args ret -> do
    args' <- mapM evalType args
    ret'  <- maybe (return Nothing) (liftM Just . evalType) ret
    return $ TProc args' ret'

  where evalToInt = liftM (toInteger . resolveInt) . evalExpr 1

-- | Evaluates a list of modifiers
evalModifiers :: [Modifier ElaboratedType] -> Simulator (Pathsum DMod2 -> Pathsum DMod2)
evalModifiers = liftM (foldr (.) (\x -> x)) . mapM go where

  go :: Modifier ElaboratedType -> Simulator (Pathsum DMod2 -> Pathsum DMod2)
  go mod = case mod of
    MInv _               -> return dagger
    MCtrl _ neg Nothing  -> return (if neg then negControlled else controlled)
    MCtrl _ neg (Just n) -> do
      let ctrl = if neg then negControlled else controlled
      i <- liftM resolveInt $ evalExpr 1 n
      return $ \ps -> (iterate ctrl ps)!!i
    MPow _ n -> do
      i <- liftM resolveInt $ evalExpr 1 n
      return $ \ps -> (iterate ((.>) ps) ps)!!(i-1)

-- | Evaluates an access path
evalAP :: SBool Var -> AccessPath ElaboratedType -> Simulator LValue
evalAP p ap = error "unimplemented"
  {-
  case ap of
  AVar _ vid -> do
    binding <- searchBinding vid
    case binding of
      VLoc i      -> LLoc i
      VLocList xs -> LLocList xs
      _           -> LID vid

  AIndex _ vid idx -> do                      -- NOTE: idx can be a range or set of indices
    binding <- searchBinding vid
    i <- liftM idxOfValue $ evalExpr p idx
    case binding of
      Nothing -> error $ "No binding for variable " ++ show vid
      Just b  -> return $ deref (valueOfBinding b) i

  -- deprecated
  AList _ aps -> do
    aps' <- mapM (evalAP p) aps
    return $ VList aps'
-}
  
-- | Evaluates an expression
evalExpr :: SBool Var -> Expr ElaboratedType -> Simulator Value
evalExpr p expr = case expr of
  EInt _ n     -> return $ VInt $ KnownI n
  EFloat _ f   -> return $ VFloat f 
  ECmplx _ c   -> return $ VCmplx c
  EBool _ b    -> return $ VBool $ KnownB b 
  EPi _        -> return $ VFloat pi
  EIm _        -> return $ VCmplx (0 :+ 1)
  EBits _ bs   -> return $ VUInt $ SymbolicUI $ SBits (map (\b -> if b then 1 else 0) bs)

  ECast _ t e  -> do
    t' <- evalType t
    v <- evalExpr p e >>= castValue t'
    return $ v

  EMeasure _ e -> do
    v <- evalExpr p e
    case v of
      VLoc l      -> liftM (VBool . SymbolicB) $ measureQ p l
      VLocList ls -> liftM (VUInt . SymbolicUI . SBits) $ mapM (measureQ p) ls

  EVar _ id   -> searchBinding id

  EIndex _ x i -> do
    x' <- evalExpr p x
    i' <- evalExpr p i
    return $ indexVal x' i'

  ESet _ l    -> do
    set <- mapM (evalExpr p) l
    return $ VList set

  ESlice _ start step stop -> do
    start' <- liftM resolveInt $ evalExpr p start
    stop'  <- liftM resolveInt $ evalExpr p stop
    step'  <- maybe (return Nothing) (liftM (Just . resolveInt) . evalExpr p) step
    case step' of
      Just s  -> return $ VList [ VInt (KnownI $ toInteger i) | i <- [start', start'+s .. stop']]
      Nothing -> return $ VList [ VInt (KnownI $ toInteger i) | i <- [start'..stop'] ]

  EUOp _ uop a -> do
    v <- evalExpr p a
    evalUop uop v

  EBOp t a bop b -> do
    v1 <- evalExpr p a
    v2 <- evalExpr p b
    evalBop v1 bop v2

  ECall _ id args -> do
    binding <- searchBinding id
    args'   <- mapM (evalExpr p) args
    case binding of
      VProc _ Nothing _ (Just summary) -> error "unimplemented"
      VProc params _ body Nothing      -> do
        locals <- openProcScope
        declareParams params args'
        ret <- simStmt p body
        restoreScope locals
        case ret of
          Nothing -> return VUnit
          Just v  -> return v

  _ -> error $ show expr

-- | Evaluates a unary operator on a value
evalUop :: UOp -> Value -> Simulator Value
evalUop op val = case (op, val) of
  (SinOp, VFloat f) -> return . VFloat $ sin f
  (CosOp, VFloat f) -> return . VFloat $ cos f
  (TanOp, VFloat f) -> return . VFloat $ tan f
  (ArccosOp, VFloat f) -> return . VFloat $ acos f
  (ArcsinOp, VFloat f) -> return . VFloat $ asin f
  (ArctanOp, VFloat f) -> return . VFloat $ atan f
  (CeilOp, VFloat f) -> return . VFloat . fromIntegral $ ceiling f
  (FloorOp, VFloat f) -> return . VFloat . fromIntegral $ floor f
  (ExpOp, VFloat f) -> return . VFloat $ exp f
  (ExpOp, VCmplx f) -> return . VCmplx $ exp f
  (LnOp, VFloat f) -> return . VFloat $ log f
  (SqrtOp, VFloat f) -> return . VFloat $ sqrt f
  (SqrtOp, VCmplx f) -> return . VCmplx $ sqrt f
  (RealOp, VCmplx f) -> return . VFloat $ realPart f
  (ImOp, VCmplx f) -> return . VFloat $ imagPart f
  (NegOp, VBool (KnownB b)) -> return . VBool . KnownB $ not b
  (NegOp, VBool (SymbolicB b)) -> return . VBool . SymbolicB $ 1 + b
  (NegOp, VInt (KnownI i)) -> return . VInt . KnownI $ complement i
  (NegOp, VInt (SymbolicI b)) -> return . VInt . SymbolicI $ complement b
  (NegOp, VUInt (KnownUI i)) -> return . VUInt . KnownUI $ complement i
  (NegOp, VUInt (SymbolicUI b)) -> return . VUInt . SymbolicUI $ complement b
  (UMinusOp, VInt (KnownI i)) -> return . VInt . KnownI $ (-i)
  (UMinusOp, VInt (SymbolicI i)) -> return . VInt . SymbolicI $ (-i)
  (UMinusOp, VUInt (KnownUI i)) -> return . VUInt . KnownUI $ (-i)
  (UMinusOp, VUInt (SymbolicUI i)) -> return . VUInt . SymbolicUI $ (-i)
  (UMinusOp, VFloat f) -> return . VFloat $ (-f)
  (UMinusOp, VCmplx f) -> return . VCmplx $ (-f)
  (PopcountOp, VUInt (KnownUI i)) -> return . VUInt . KnownUI . fromIntegral $ popCount i
  (PopcountOp, VUInt (SymbolicUI i)) -> return . VUInt . SymbolicUI $ sPopcount i
  _ -> error "Runtime error: invalid unary operation"

-- | Evaluates a binary operator on values
evalBop :: Value -> BinOp -> Value -> Simulator Value
evalBop v1 op v2 = case (op, v1, v2) of
  (AndOp, VBool b1, VBool b2) -> error "unimplemented"
  {-
data BinOp = AndOp -- &, &&
           | OrOp  -- |, ||
           | XorOp -- ^
           | LShiftOp  -- <<
           | RShiftOp -- >>
           | LRotOp  -- rotl
           | RRotOp -- rotr
           | EqOp -- ==
           | NEqOp -- !=
           | LTOp -- <
           | LEqOp -- <=
           | GTOp -- >
           | GEqOp -- >=
           | PlusOp -- +
           | MinusOp -- -
           | TimesOp -- *
           | DivOp -- / 
           | ModOp -- %
           | PowOp -- **
           | ConcatOp -- ++, not used in openQASM 3 spec
-}
  
-- | Simulates a declaration
simDecl :: Decl ElaboratedType -> Simulator ()
simDecl decl = case decl of

  DVar vid typ maybeExpr True -> do
      _   <- evalType typ
      val <- evalExpr 1 $ fromJust maybeExpr
      declare True vid val

  DVar vid typ (Just expr) False -> do
      _   <- evalType typ
      val <- evalExpr 1 expr
      declare False vid val

  DVar vid typ Nothing False -> do
      typ <- evalType typ
      val <- allocVar vid typ
      declare False vid val

  DDef did dparams dreturns dbody -> do
    dreturns' <- mapM evalType dreturns
    dparams'  <- traverse (\(a, x) -> (,) a <$> evalType x) dparams
    declare True did (VProc dparams' dreturns' dbody Nothing)

  DGate gid gparams gqargs gbody -> do
    let params = zip gparams (repeat $ TFloat Nothing) ++ zip gqargs (repeat TQBit)
    declare True gid (VProc params Nothing gbody Nothing)

  DExtern _ _ _ -> error "TODO"

  DAlias  _ _   -> error "TODO"

-- | Simulate a statement
simStmt :: SBool Var -> Stmt ElaboratedType -> Simulator (Maybe Value)
simStmt p stmt = case stmt of
  SSkip _                    -> return Nothing
  SBarrier _ _               -> return Nothing
  SPragma _ _                -> return Nothing

  SBlock _ stmts             -> do
    openScope
    foldM (\m s -> (liftM $ mplus m) $ simStmt p s) Nothing stmts
    closeScope
    return Nothing

  SWhile _ cond stmt         -> error "While loops currently unsupported"

  SIf _ cond stmtT stmtE     -> do
    q <- evalExpr p cond
    case q of
      VBool (KnownB b)    -> if b then simStmt p stmtT else simStmt p stmtE
      VBool (SymbolicB b) -> do
        simStmt (p*b) stmtT
        simStmt (p*(1+b)) stmtE
  
  SFor _ (id, typ) expr stmt -> do
    v <- evalExpr p expr
    ty <- evalType typ
    case v of
      VList list -> do
        let iter ret val = (liftM $ mplus ret) (declare False id val >> simStmt p stmt)
        openScope
        foldM iter Nothing list
        closeScope
        return Nothing
      _          -> error "Fatal: couldn't reduce for loop to a list"

  SReset _ (EVar _ id)       -> do
    binding <- searchBinding id
    case binding of
      VLoc l      -> resetQ p l
      VLocList ls -> mapM_ (resetQ p) ls
    return Nothing

  SDeclare _ decl            -> if p == 1 then
                                  simDecl decl >> return Nothing
                                else
                                  error "invalid stmt in symbolic branch"

  SAssign _ ap expr -> error "unimplemented"
    
  SGateCall _ mods gid cs qs -> do
    cs'  <- mapM (evalExpr p) cs
    qs'  <- mapM (liftM resolveLoc . evalAP p) qs
    mod' <- evalModifiers mods
    gate <- generateGate gid cs'
    applyBlock p qs' (mod' gate)
    return Nothing
      
  SAnnotated _ annots stmt   -> simStmt p stmt

  SReturn _ (Just e)         -> liftM Just $ evalExpr p e
  SReturn _ Nothing          -> return $ Just VUnit
  SExpr _ expr               -> evalExpr p expr >> return Nothing

-- | Simulates a program
simProg :: Prog ElaboratedType -> Simulator (Maybe Value)
simProg (Prog _ stmts) =
  foldM (\m s -> (liftM $ mplus m) $ simStmt 1 s) Nothing stmts

{-----------------------------
 Testing
 -----------------------------}

-- | Convenience definition for testing
simulate :: Prog ElaboratedType -> IO ()
simulate prog = do
  let (_,env) = runState (simProg prog) initEnv
  print env
