{-|
Module      : SymExec
Description : Symbolic execution engine
Copyright   : (c) Matthew Amy, 2026
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

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
type SimInteger  = Either Integer (SInt Var) 
type SimUInteger = Either Integer (SUInt Var)
type SimBool     = Either Bool    (SBool Var)

-- | Co-products with a promotion
class SymbolicRepr c t | t -> c where
  symbolicRepr :: c -> t
  concretize :: Either c t -> Maybe c

instance SignBit (SBits a v) v => SymbolicRepr Integer (SBits a v) where
  symbolicRepr = makeSymbolic
  concretize   = either (Just) (fromSymbolic)

instance SymbolicRepr Bool (SBool Var) where
  symbolicRepr = \b -> if b then 1 else 0
  concretize   = either (Just) (fromSymbolicPoly) where
    fromSymbolicPoly b = if isConstant b then Just (1 == b) else Nothing

pattern Concrete c <- Left c where
  Concrete c = Left c

pattern Symbolic c <- Right c where
  Symbolic c = Right c

-- | Promotes a symbolic
promoteRepr :: SymbolicRepr c t => Either c t -> Either c t
promoteRepr = either (Symbolic . symbolicRepr) (Symbolic)

-- | Unifies the representation of two symbolic types
unifyRepr :: SymbolicRepr c t => Either c t -> Either c t -> Either (c,c) (t,t)
unifyRepr a b  = case (a,b) of
  (Concrete a', Concrete b') -> Concrete (a',b')
  (Concrete a', Symbolic b') -> Symbolic (symbolicRepr a', b')
  (Symbolic a', Concrete b') -> Symbolic (a', symbolicRepr b')
  (Symbolic a', Symbolic b') -> Symbolic (a', b')

-- | Shorthand for applying a unary operator on a symbolic representation
applyUnary :: (c -> c') -> (t -> t') -> Either c t -> Either c' t'
applyUnary a b = either (Left . a) (Right . b)

-- | Shorthand for applying a binary operator on a symbolic representation
applyBinary :: SymbolicRepr c t =>
               (c -> c -> c') ->
               (t -> t -> t') ->
               (Either c t -> Either c t -> Either c' t')
applyBinary a b e = either (Left . uncurry a) (Right . uncurry b) . unifyRepr e

-- | Utility for casting symbolic values
castS :: Maybe a -> a
castS Nothing  = error "Runtime conversion from symbolic to non-symbolic value"
castS (Just a) = a

instance SignBit (SBits a v) v => Num (Either Integer (SBits a v)) where
  (+)         = applyBinary (+) (+)
  (*)         = applyBinary (*) (*)
  negate      = applyUnary negate negate
  abs         = applyUnary abs abs
  signum      = applyUnary signum signum
  fromInteger = Concrete

instance SignBit (SBits a v) v => Bits (Either Integer (SBits a v)) where
  (.&.)        = applyBinary (.&.) (.&.)
  (.|.)        = applyBinary (.|.) (.|.)
  xor          = applyBinary xor xor
  complement   = applyUnary complement complement
  shift a b    = applyUnary (\a -> shift a b) (\a -> shift a b) a
  rotate a b   = applyUnary (\a -> rotate a b) (\a -> rotate a b) a 
  bitSize      = either bitSize bitSize
  bitSizeMaybe = either bitSizeMaybe bitSizeMaybe
  isSigned     = either isSigned isSigned
  testBit      = error "Unimplemented"
  bit          = error "Unimplemented"

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

-- | Indexes a value
indexVal :: Value -> Value -> Value
indexVal val idx = case (val, resolve idx) of
    (VLocList xs, Concrete j)  -> VLoc $ xs!!j
    (VLocList xs, Symbolic js) -> VLocList $ [xs!!j | j <- js]
    (VInt si, Concrete j)      -> case si of
      Concrete i -> VUInt . Concrete $ if testBit i j then 1 else 0
      Symbolic i -> VUInt . Symbolic . SBits $ [testBitS i j]
    (VInt si, Symbolic js)     -> case si of
      Concrete i -> VUInt . Concrete $ fromBits [if testBit i j then 1 else 0 | j <- js]
      Symbolic i -> VUInt . Symbolic . SBits $ [testBitS i j | j <- js]
    (VUInt si, Concrete j)     -> case si of
      Concrete i -> VUInt . Concrete $ if testBit i j then 1 else 0
      Symbolic i -> VUInt . Symbolic . SBits $ [testBitS i j]
    (VUInt si, Symbolic js)    -> case si of
      Concrete i -> VUInt . Concrete $ fromBits [if testBit i j then 1 else 0 | j <- js]
      Symbolic i -> VUInt . Symbolic . SBits $ [testBitS i j | j <- js]
    _                       -> error "non indexable expression"
  where resolve idx = case idx of
          VList ids -> Symbolic $ map resolveInt ids
          _         -> Concrete $ resolveInt idx
        fromBits    = foldr (+) 0 . map foo . zip [0..]
        foo (i,b)   = b `shiftL` i

-- | Resolves a value to a (non-symbolic) integer
resolveInt :: Value -> Int
resolveInt val = case val of
  VInt si  -> fromIntegral $ castS $ concretize si
  VUInt si -> fromIntegral $ castS $ concretize si
  VBool sb -> if (castS $ concretize sb) then 1 else 0
  _        -> error "Unexpected non-integral expression"

-- | Resolves an l-value to a location
resolveLoc :: LValue -> Integer
resolveLoc lval = case lval of
  LLoc i -> fromIntegral i
  _      -> error "Unexpected lvalue expression"

-- | Promotes a bit to an int
intOfBit :: Bool -> Integer
intOfBit b = if b then 1 else 0

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
    return $ VUInt $ Symbolic $ SBits [ofVar (FVar $ fvar id i) | i <- [0..l-1]]
  TInt Nothing  -> return VUndefined
  TInt (Just l) -> do
    id <- freshen id
    return $ VInt $ Symbolic $ SBits [ofVar (FVar $ fvar id i) | i <- [0..l-1]]
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
    VBool _  -> return val
    VInt  i  -> return . VBool $ applyUnary (/= 0) (flip testBitS 0) i
    VUInt  i -> return . VBool $ applyUnary (/= 0) (flip testBitS 0) i
    VFloat f -> return . VBool . Concrete $ f /= 0.0
      
  TInt m -> case val of
    VBool b     -> return . VInt $ applyUnary (intOfBit) (setWidthM m . SBits . (:[])) b
    VInt i      -> return . VInt $ applyUnary (id) (setWidthM m) i
    VUInt i     -> return . VInt $ applyUnary (id) (setWidthM m . promoteUnsigned) i
    VFloat f    -> return . VInt . Concrete . truncate $ f
    VLoc l      -> lookupLoc l >>= return . VInt . Symbolic . setWidthM m . SBits . (:[])
    VLocList xs -> mapM lookupLoc xs >>= return . VInt . Symbolic . setWidthM m . SBits

  TUInt m -> case val of
    VBool b     -> return . VUInt $ applyUnary (intOfBit) (setWidthM m . SBits . (:[])) b
    VInt i      -> return . VUInt $ applyUnary (unsign) (setWidthM m . convertSign) i
    VUInt i     -> return . VUInt $ applyUnary (id) (setWidthM m) i
    VFloat f    -> return . VUInt . Concrete . truncate $ f
    VLoc l      -> lookupLoc l >>= return . VUInt . Symbolic . setWidthM m . SBits . (:[])
    VLocList xs -> mapM lookupLoc xs >>= return . VUInt . Symbolic . setWidthM m . SBits

  TFloat _ -> case val of
    VInt si  -> return . VFloat . fromIntegral . castS . concretize $ si
    VUInt si -> return . VFloat . fromIntegral . castS . concretize $ si
    VFloat f -> return val
    VBool sb -> return . VFloat . fromIntegral . intOfBit . castS . concretize $ sb

  TAngle _ -> case val of
    VFloat f  -> return . VFloat $ f / pi

  -- Allocate space in memory
  TCReg m -> case val of
    VInt  i     -> return . VBool . applyUnary (/= 0) (flip testBitS 0) $ i
    VUInt i     -> return . VBool . applyUnary (/= 0) (flip testBitS 0) $ i
    VLocList ks -> return val

  _ -> error "Runtime cast error"
  
  where unsign i = case i < 0 of
          True  -> error "Casting negative value to unsigned integer"
          False -> i
        setWidthM Nothing  si = si
        setWidthM (Just m) si = setWidth si (fromIntegral m)

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

  TUInt me  -> liftM TUInt  $ maybe (return Nothing) (liftM Just . evalToInt) me
  TInt me   -> liftM TInt   $ maybe (return Nothing) (liftM Just . evalToInt) me
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
  EInt _ n     -> return $ VInt $ Concrete n
  EFloat _ f   -> return $ VFloat f 
  ECmplx _ c   -> return $ VCmplx c
  EBool _ b    -> return $ VBool $ Concrete b 
  EPi _        -> return $ VFloat pi
  EIm _        -> return $ VCmplx (0 :+ 1)
  EBits _ bs   -> return $ VUInt $ Symbolic $ SBits (map (\b -> if b then 1 else 0) bs)

  ECast _ t e  -> do
    t' <- evalType t
    v <- evalExpr p e >>= castValue t'
    return $ v

  EMeasure _ e -> do
    v <- evalExpr p e
    case v of
      VLoc l      -> liftM (VBool . Symbolic) $ measureQ p l
      VLocList ls -> liftM (VUInt . Symbolic . SBits) $ mapM (measureQ p) ls

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
      Just s  -> return $ VList [ VInt (Concrete $ toInteger i) | i <- [start', start'+s .. stop']]
      Nothing -> return $ VList [ VInt (Concrete $ toInteger i) | i <- [start'..stop'] ]

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
  (NegOp, VBool b) -> return . VBool $ applyUnary (not) (1+) b
  (NegOp, VInt i) -> return . VInt $ complement i
  (NegOp, VUInt i) -> return . VUInt $ complement i
  (UMinusOp, VInt i) -> return . VInt $ negate i
  (UMinusOp, VUInt i) -> return . VUInt $ negate i
  (UMinusOp, VFloat f) -> return . VFloat $ (-f)
  (UMinusOp, VCmplx f) -> return . VCmplx $ (-f)
  (PopcountOp, VUInt i) -> return . VUInt $ applyUnary (fromIntegral . popCount) (sPopcount) i
  _ -> error "Runtime error: invalid unary operation"

-- | Evaluates a binary operator on values
evalBop :: Value -> BinOp -> Value -> Simulator Value
evalBop v1 op v2 = case (op, v1, v2) of
  (AndOp, VBool b1, VBool b2)   -> return . VBool $ applyBinary (&&) (*) b1 b2
  (AndOp, VInt i1, VInt i2)     -> return . VInt $ i1 .&. i2
  (AndOp, VUInt i1, VUInt i2)   -> return . VUInt $ i1 .&. i2

  (OrOp, VBool b1, VBool b2)    -> return . VBool $ applyBinary (||) (\a b -> a + b + a*b) b1 b2
  (OrOp, VInt i1, VInt i2)      -> return . VInt $ i1 .|. i2
  (OrOp, VUInt i1, VUInt i2)    -> return . VUInt $ i1 .|. i2

  (XorOp, VBool b1, VBool b2)   -> return . VBool $ applyBinary (xor) (+) b1 b2
  (XorOp, VInt i1, VInt i2)     -> return . VInt $ i1 `xor` i2
  (XorOp, VUInt i1, VUInt i2)   -> return . VUInt $ i1 `xor` i2

  -- Differs from the specs (defined by uint, int arguments)
  (LShiftOp, VUInt i1, VUInt i2) -> let shiftL' a = shift a . fromIntegral  in
    return . VUInt $ applyBinary (shiftL') (sLShift) i1 i2
  (RShiftOp, VUInt i1, VUInt i2) -> let shiftR' a = shift a . fromIntegral  in
    return . VUInt $ applyBinary (shiftR') (sRShift) i1 i2

  -- Differs from the specs (defined by uint, int arguments)
  (LRotOp, VUInt i1, VUInt i2) -> let rotateL' a = rotateL a . fromIntegral  in
    return . VUInt $ applyBinary (rotateL') (sLRot) i1 i2
  (RRotOp, VUInt i1, VUInt i2) -> let rotateR' a = rotateR a . fromIntegral  in
    return . VUInt $ applyBinary (rotateR') (sRRot) i1 i2

  (EqOp, VBool b1, VBool b2)    -> return . VBool $ applyBinary (==) (\a b -> 1 + a + b) b1 b2
  (EqOp, VInt i1, VInt i2)      -> return . VBool $ applyBinary (==) (sEq) i1 i2
  (EqOp, VUInt i1, VUInt i2)    -> return . VBool $ applyBinary (==) (sEq) i1 i2
  (EqOp, VFloat f1, VFloat f2)  -> return . VBool . Concrete $ f1 == f2
  (EqOp, VCmplx c1, VCmplx c2)  -> return . VBool . Concrete $ c1 == c2

  (LTOp, VBool b1, VBool b2)    -> return . VBool $ applyBinary (<) (\a b -> (1+a)*b) b1 b2
  (LTOp, VInt i1, VInt i2)      -> return . VBool $ applyBinary (<) (sLT) i1 i2
  (LTOp, VUInt i1, VUInt i2)    -> return . VBool $ applyBinary (<) (sLT) i1 i2
  (LTOp, VFloat f1, VFloat f2)  -> return . VBool . Concrete $ f1 < f2

  (LEqOp, VBool b1, VBool b2)    -> return . VBool $ applyBinary (<=) (\a b -> 1 + a*(1+b)) b1 b2
  (LEqOp, VInt i1, VInt i2)      -> return . VBool $ applyBinary (<=) (sLEq) i1 i2
  (LEqOp, VUInt i1, VUInt i2)    -> return . VBool $ applyBinary (<=) (sLEq) i1 i2
  (LEqOp, VFloat f1, VFloat f2)  -> return . VBool . Concrete $ f1 <= f2

  (GTOp, VBool b1, VBool b2)    -> return . VBool $ applyBinary (>) (\a b -> a*(1+b)) b1 b2
  (GTOp, VInt i1, VInt i2)      -> return . VBool $ applyBinary (>) (sGT) i1 i2
  (GTOp, VUInt i1, VUInt i2)    -> return . VBool $ applyBinary (>) (sGT) i1 i2
  (GTOp, VFloat f1, VFloat f2)  -> return . VBool . Concrete $ f1 > f2

  (GEqOp, VBool b1, VBool b2)    -> return . VBool $ applyBinary (>=) (\a b -> 1 + (1+a)*b) b1 b2
  (GEqOp, VInt i1, VInt i2)      -> return . VBool $ applyBinary (>=) (sGEq) i1 i2
  (GEqOp, VUInt i1, VUInt i2)    -> return . VBool $ applyBinary (>=) (sGEq) i1 i2
  (GEqOp, VFloat f1, VFloat f2)  -> return . VBool . Concrete $ f1 >= f2

  (PlusOp, VBool b1, VBool b2)    -> return . VBool $ applyBinary (xor) (+) b1 b2
  (PlusOp, VInt i1, VInt i2)      -> return . VInt $ applyBinary (+) (+) i1 i2
  (PlusOp, VUInt i1, VUInt i2)    -> return . VUInt $ applyBinary (+) (+) i1 i2
  (PlusOp, VFloat f1, VFloat f2)  -> return . VFloat $ f1 + f2
  (PlusOp, VCmplx c1, VCmplx c2)  -> return . VCmplx $ c1 + c2

  (MinusOp, VBool b1, VBool b2)    -> return . VBool $ applyBinary (xor) (+) b1 b2
  (MinusOp, VInt i1, VInt i2)      -> return . VInt $ applyBinary (-) (-) i1 i2
  (MinusOp, VUInt i1, VUInt i2)    -> return . VUInt $ applyBinary (-) (-) i1 i2
  (MinusOp, VFloat f1, VFloat f2)  -> return . VFloat $ f1 - f2
  (MinusOp, VCmplx c1, VCmplx c2)  -> return . VCmplx $ c1 - c2

  (TimesOp, VBool b1, VBool b2)    -> return . VBool $ applyBinary (&&) (*) b1 b2
  (TimesOp, VInt i1, VInt i2)      -> return . VInt $ applyBinary (*) (*) i1 i2
  (TimesOp, VUInt i1, VUInt i2)    -> return . VUInt $ applyBinary (*) (*) i1 i2
  (TimesOp, VFloat f1, VFloat f2)  -> return . VFloat $ f1 * f2
  (TimesOp, VCmplx c1, VCmplx c2)  -> return . VCmplx $ c1 * c2

  (DivOp, VInt i1, VInt i2)      -> return . VInt $ applyBinary (quot) (sQuot) i1 i2
  (DivOp, VUInt i1, VUInt i2)    -> return . VUInt $ applyBinary (quot) (sQuot) i1 i2
  (DivOp, VFloat f1, VFloat f2)  -> return . VFloat $ f1 / f2
  (DivOp, VCmplx c1, VCmplx c2)  -> return . VCmplx $ c1 / c2

  (ModOp, VInt i1, VInt i2)      -> return . VInt $ applyBinary (rem) (sMod) i1 i2
  (ModOp, VUInt i1, VUInt i2)    -> return . VUInt $ applyBinary (rem) (sMod) i1 i2
  (ModOp, VFloat f1, VFloat f2)  -> return . VFloat $ f1 - f2 * fromIntegral (floor $ f1 / f2)

  (PowOp, VInt i1, VInt i2)      -> return . VInt $ applyBinary (^) (sPow) i1 i2
  (PowOp, VUInt i1, VUInt i2)    -> return . VUInt $ applyBinary (^) (sPow) i1 i2
  (PowOp, VFloat f1, VFloat f2)  -> return . VFloat $ f1 ** f2
  (PowOp, VCmplx c1, VCmplx c2)  -> return . VCmplx $ c1 ** c2

  (ConcatOp, VLocList l1, VLocList l2) -> return . VLocList $ l1 ++ l2

  _  -> error "Bad operands to binary operator"
  
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
      VBool (Concrete b)    -> if b then simStmt p stmtT else simStmt p stmtE
      VBool (Symbolic b) -> do
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

  SDeclare _ decl -> if p == 1 then
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
