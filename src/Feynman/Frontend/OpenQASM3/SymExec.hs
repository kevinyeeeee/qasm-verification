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
  
import Data.Functor.Identity (Identity)

import Data.Complex
import Data.Maybe (fromJust)
import Data.Bits

import Control.Monad.State.Strict hiding (lift)

import Feynman.Core (ID, discretize, Angle(..))
import Feynman.Algebra.Base
import Feynman.Algebra.Pathsum.Balanced
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Algebra.SArith

import Feynman.Frontend.OpenQASM3.Core
import Feynman.Frontend.OpenQASM3.TypeCheck

import qualified Feynman.Util.Unicode as U

{-----------------------------
 Data types
 -----------------------------}

-- | Monadic interface for symbolic executions
type SymExecM m = StateT SimEnv m

-- | Basic simulator type
type Simulator = SymExecM Identity

-- | Execution environment
data SimEnv = SimEnv {
  pathsum :: Pathsum DMod2,
  globals :: Map ID Binding,
  locals :: [Map ID Binding],
  qwidth :: Int -- number of allocated qubits
} deriving (Show)

-- | Different types of bindings
data Binding =
    Symbolic { typ :: Type,
               offset :: Integer }
  | Scalar { typ :: Type,
             value :: Value }
  | Block { typ :: Type,
            params :: [(ID, Type)],
            returns :: Maybe Type,
            body :: Stmt ElaboratedType,
            summary :: Maybe (Pathsum DMod2) }
  | Gate { typ :: Type,
           gparams :: [ID],
           gargs :: [ID],
           body :: Stmt ElaboratedType,
           summary :: Maybe (Pathsum DMod2) }
  deriving (Show)

-- | Value types
data Value =
    VInt Integer
  | VPi
  | VIm
  | VBool Bool
  | VList [Value]
  | VFloat Double
  | VCmplx (Complex Double)
  | VQBit Integer
  | VQReg Integer Integer -- offset, size
  | VCBit Integer
  | VCReg Integer Integer
  | VPoly (SBool Var)
  | VPolyList [SBool Var]
  | VUnit
  deriving (Show)

{- Redesigned value types -}

{-

data SimInteger = KnownI Integer   | SymbolicI [SBool Var]
data SimUInteger = KnownUI Integer | SymbolicUI [SBool Var]
data SimBool = KnownBool Bool      | SymbolicBool Bool

data Value =
    VUnit
  | VLoc Integer
  | VInt SimInteger
  | VUInt SimUInteger
  | VBool SimBool
  | VList [Value]
  | VFloat Double
  | VCmplx (Complex Double)
  | VProc { typ :: Type,
            params :: [(ID, Type)],
            returns :: Maybe Type
            body :: Stmt ElaboratedType,
            summary :: Maybe (Pathsum DMod2) }
  deriving (Show)

-- | Allocates space on the quantum or classical heap
alloc :: Bool -> Int -> Simulator Int
alloc isQ size = modify go where
  go env = case isQ of
    True -> 

-}

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
  
-- | Adds a globally scoped binding
bindGlobal :: ID -> Binding -> Simulator ()
bindGlobal id bind = modify $ \env -> env { globals = Map.insert id bind (globals env) }

-- | Adds a locally scoped binding
bindVar :: ID -> Binding -> Simulator ()
bindVar id bind = do
  env <- get
  let (b:bs) = locals env
  put $ env { locals = (Map.insert id bind b) : bs }

-- | Finds a binding in the environment
searchBinding :: ID -> Simulator (Maybe Binding)
searchBinding id = get >>= \env -> return $ search $ (globals env : locals env)
  where search = msum . map (Map.lookup id)

-- | Retrieves the value of a binding
valueOfBinding :: Binding -> Value
valueOfBinding b = case b of
  Scalar typ val -> val

  Symbolic (TCReg i) offset -> VCReg offset i
  Symbolic TBool offset -> VQBit offset

  Symbolic (TQReg i) offset -> VQReg offset i
  Symbolic TQBit offset -> VQBit offset

  Symbolic (TUInt (Just i)) offset -> VCReg offset i
  Symbolic (TInt (Just i)) offset -> VCReg offset i 
  Symbolic (TAngle (Just i)) offset -> VCReg offset i
  Symbolic (TFloat (Just i)) offset -> VCReg offset i
  Symbolic (TCmplx (Just i)) offset -> VCReg offset i

  _ -> error "Value of block or gate binding"

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

-- | Binds parameters of a function
bindParams :: [(ID, Type)] -> [Value] -> Simulator ()
bindParams params args = mapM_ go $ zip params args where
  go ((id,ty),val) = case (ty,val) of
    (TBool  , VCBit loc)     -> bindVar id (Symbolic ty loc)
    (TCReg i, VCReg loc len) -> bindVar id (Symbolic ty loc)
    (TQBit,   VQBit loc)     -> bindVar id (Symbolic ty loc)
    (TQReg i, VQReg loc len) -> bindVar id (Symbolic ty loc)
    (TBool,   VBool _)       -> bindVar id (Scalar ty val)
    (TUInt i, VInt j)        -> bindVar id (Scalar ty val)
    (TUInt i, VPoly j)       -> error "unimplemented"
    (TInt i,  VInt j)        -> bindVar id (Scalar ty val)
    (TInt i,  VPoly j)       -> error "unimplemented"
    (TAngle i, VFloat j)     -> bindVar id (Scalar ty val)
    (TFloat i, VFloat j)     -> bindVar id (Scalar ty val)
    (TCmplx i, VCmplx j)     -> bindVar id (Scalar ty val)
    

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
   ("gphase", \[o] -> globalPhase (evalAngle o)),
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
          VPi -> fromDyadic . discretize . Continuous $ pi
          VBool b ->  fromDyadic . discretize . Continuous $ fromInteger (if b then 1 else 0)
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
applyBlock :: SBool Var -> [Value] -> Pathsum DMod2 -> Simulator ()
applyBlock p args ps = do
  qoffsets <- liftM (concat . map fromJust) $ mapM getQVarOffsets args
  coffsets <- liftM (concat . map fromJust) $ mapM getCVarOffsets args
  qwidth <- getQWidth
  let offsets = qoffsets ++ [i+qwidth | i <- qoffsets] ++ coffsets
  modify $ \env -> env { pathsum = applyPControlled ps p offsets (pathsum env) }

-- | Generates a path sum for a basic gate
generateGate :: ID -> [Value] -> Simulator (Pathsum DMod2)
generateGate id cargs = case Map.lookup id stdlib of
  Just ps -> return $ ps cargs
  Nothing -> do
    binding <- searchBinding id
    case binding of
      Just (Gate _ _ _ _ (Just ps))          -> return ps
      Just (Gate _ params args body Nothing) -> error "Unimplemented" -- do
        -- Generate a summary of the gate
        -- env <- get
        -- put $ env { pathsum = mempty, qwidth = 0, locals = [Map.empty] }
        -- bindParams (zip params (repeat (TAngle Nothing))) cargs
        
{-----------------------------
 Casting & data operations
 -----------------------------}

-- | Casts a value of one type as another type
castValue :: ElaboratedType -> Value -> Value
castValue (EType ty _ _) val = case (ty, val) of
  (TFloat _, VPi        ) -> VFloat pi
  (TFloat _, VInt i     ) -> VFloat $ fromIntegral i
  (TFloat _, VFloat f   ) -> VFloat f
  (TFloat _, VBool False) -> VFloat 0.0
  (TFloat _, VBool True ) -> VFloat 1.0
  (TUInt  _, VInt i     ) -> VInt i
  (TInt   _, VInt i     ) -> VInt i
  (TBool   , VPoly p    ) -> VPoly p
  (TRange _, VList l    ) -> VList l
  _ -> val

-- | Gets the integer value of an index
idxOfValue :: Value -> Integer
idxOfValue (VInt i) = i
idxOfValue _ = error "Non-integral index value"

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

  where evalToInt e = evalExpr 1 e >>= \(VInt n) -> return n

-- | Evaluates a list of modifiers
evalModifiers :: [Modifier ElaboratedType] -> Simulator (Pathsum DMod2 -> Pathsum DMod2)
evalModifiers = liftM (foldr (.) (\x -> x)) . mapM go where

  go :: Modifier ElaboratedType -> Simulator (Pathsum DMod2 -> Pathsum DMod2)
  go mod = case mod of
    MInv _               -> return dagger
    MCtrl _ neg Nothing  -> return (if neg then negControlled else controlled)
    MCtrl _ neg (Just n) -> do
      let ctrl = if neg then negControlled else controlled
      v <- evalExpr 1 n
      case v of
        VInt i -> return $ \ps -> (iterate ctrl ps)!!(fromInteger i)
        _      -> error "Invalid number of controls"
    MPow _ n -> do
      v <- evalExpr 1 n
      case v of
        VInt i -> return $ \ps -> (iterate ((.>) ps) ps)!!(fromInteger $ i-1)
        _      -> error "Invalid number of controls"

-- | Evaluates an access path
evalAP :: SBool Var -> AccessPath ElaboratedType -> Simulator Value
evalAP p ap = case ap of
  AVar _ vid -> do
    binding <- searchBinding vid
    case binding of
      Nothing -> error $ "No binding for variable " ++ show vid
      Just b  -> return $ valueOfBinding b

  AIndex _ vid idx -> do
    binding <- searchBinding vid
    i <- liftM idxOfValue $ evalExpr p idx
    case binding of
      Nothing -> error $ "No binding for variable " ++ show vid
      Just b  -> return $ deref (valueOfBinding b) i

  -- deprecated
  AList _ aps -> do
    aps' <- mapM (evalAP p) aps
    return $ VList aps'

-- | Evaluates an expression
evalExpr :: SBool Var -> Expr ElaboratedType -> Simulator Value
evalExpr p expr = case expr of
  EInt _ n     -> return $ VInt n
  EFloat _ f   -> return $ VFloat f 
  ECmplx _ c   -> return $ VCmplx c
  EBool _ b    -> return $ VBool b 
  EPi _        -> return $ VPi
  EIm _        -> return $ VIm
  EBits _ bs   -> return $ VPolyList (map (\b -> if b then 1 else 0) bs)

  ECast t _ e  -> do
    v <- evalExpr p e
    return $ castValue t v

  EMeasure _ e -> do
    v <- evalExpr p e
    case v of
      VQBit i -> liftM VPoly $ measureQ p i
      VQReg i size -> liftM VPolyList $ mapM (measureQ p) [i..i+size-1]

  EVar _ id   -> do
    binding <- searchBinding id
    case binding of
      Nothing                    -> error $ "No binding for variable " ++ show id
      Just (Scalar _ e)          -> return e
      Just (Symbolic typ offset) -> case typ of
        TCReg n -> return $ VCReg offset n
        TBool   -> return $ VCBit offset
        TQBit   -> return $ VQBit offset
        TQReg n -> return $ VQReg offset n
        TUInt (Just n) -> return $ VCReg offset n
        _       -> error "invalid symbolic type"

  EVarDec t vid typeExpr -> do
    ty <- evalType typeExpr
    let v = case ty of
          TBool          -> VPoly (ofVar $ FVar vid)
          TCReg n        -> VPolyList [ ofVar $ FVar (fvar vid i) | i <- [0..n-1] ]
          TUInt (Just n) -> VPolyList [ ofVar $ FVar (fvar vid i) | i <- [0..n-1] ]
          _              -> error "Invalid variable declaration"
    bindVar vid $ Scalar ty v
    return $ v

  EIndex _ x i -> do
    x' <- evalExpr p x
    i' <- evalExpr p i
    case (x', i') of
      (VPolyList l      , VInt i) -> return $ VPoly (l !! (fromInteger i))
      (VQReg offset size, VInt i) ->
        if i < toInteger size then
          return $ VQBit (offset + i)
        else
          error "index out of range"
      (VCReg offset size, VInt i) ->
        if i < toInteger size then
          return $ VCBit (offset + i)
        else
          error "index out of range"
      (VList l          , VInt i) -> return $ l !! (fromInteger i)
      _                       -> error "non indexable expression"

  ESet _ l    -> do
    set <- mapM (evalExpr p) l
    return $ VList set

  ESlice _ start step stop -> do
    ~(VInt start') <- evalExpr p start
    ~(VInt stop')  <- evalExpr p stop
    step'          <- maybe (return Nothing) (liftM Just . evalExpr p) step
    case step' of
      Just (VInt s) -> return $ VList [ VInt (i*s) | i <- [start'..stop'],  i*s <= stop']
      Nothing       -> return $ VList [ VInt i | i <- [start'..stop'] ]

  EUOp _ uop a -> do
    v <- evalExpr p a
    return $ evalUop uop v

  EBOp t a bop b -> do
    v1 <- evalExpr p a
    v2 <- evalExpr p b
    return $ evalBop v1 bop v2

  ECall _ id args -> do
    binding <- searchBinding id
    args'   <- mapM (evalExpr p) args
    case binding of
      Just (Block _ _ Nothing _ (Just summary)) -> applyBlock p args' summary >> return VUnit
      Just (Block _ params ret body _)          -> do
        openScope
        bindParams params args'
        ret <- simStmt p body
        closeScope
        case ret of
          Nothing -> return VUnit
          Just v  -> return v

  _ -> error $ show expr

-- | Evaluates a unary operator on a value
evalUop :: UOp -> Value -> Value
evalUop _ _ = error "Unimplemented"

-- | Evaluates a binary operator on values
evalBop :: Value -> BinOp -> Value -> Value
evalBop _ _ _ = error "Unimplemented"

-- | Simulates a declaration
simDecl :: Decl ElaboratedType -> Simulator ()
simDecl _ = error "Unimplemented"

-- | Simulate a statement
simStmt :: SBool Var -> Stmt ElaboratedType -> Simulator (Maybe Value)
simStmt p stmt = case stmt of
  SSkip _                    -> return Nothing
  SBarrier _ _               -> return Nothing
  SPragma _ _                -> return Nothing

  SBlock _ stmts             -> foldM (\m s -> (liftM $ mplus m) $ simStmt p s) Nothing stmts

  SWhile _ cond stmt         -> error "While loops currently unsupported"

  SIf _ cond stmtT stmtE     -> do
    q <- evalExpr p cond
    case q of
      VBool True -> simStmt p stmtT
      VBool False -> simStmt p stmtE
      VPoly q     -> do
        simStmt (p*q) stmtT
        simStmt (p*(1+q)) stmtE
      _ -> error "Fatal: couldn't reduce condition to Boolean"
  
  SFor _ (id, typ) expr stmt -> do
    v <- evalExpr p expr
    ty <- evalType typ
    case v of
      VList list -> do
        let iter ret i = (liftM $ mplus ret) (bindVar id (Scalar ty i) >> simStmt p stmt)
        openScope
        ret <- foldM iter Nothing list
        closeScope
        return ret
        
      _          -> error "Fatal: couldn't reduce for loop to a list"

  SReset _ (EVar _ id)       -> do
    binding <- searchBinding id
    case binding of
      Nothing                          -> error $ "No binding for variable " ++ show id
      Just (Symbolic TQBit offset)     -> (resetQ p) offset
      Just (Symbolic (TQReg n) offset) -> mapM_ (resetQ p) [offset..offset+(fromInteger n)-1]
    return Nothing

  SDeclare _ decl            -> if p == 1 then
                                  simDecl decl >> return Nothing
                                else
                                  error "invalid stmt in symbolic branch"

  SAssign _ (AVar _ id) expr -> do
    v <- evalExpr p expr
    binding <- searchBinding id
    case binding of
      Nothing                          -> error $ "No binding for variable " ++ show id

      Just (Scalar typ _)              ->
        if p == 1 then
          assignScalar id typ v
        else
          error "Can't modify non-symbolic value inside a symbolic branch"

      Just (Symbolic typ offset) ->
        assignSymbolic p typ offset v
    return Nothing
      

  SAssign _ (AIndex _ id i) expr -> do
    i' <- evalExpr p i
    v <- evalExpr p expr
    binding <- searchBinding id
    case (binding, i') of
      (Nothing, _)                         -> error $ "No binding for variable " ++ show id

      (Just (Symbolic typ offset), VInt j) ->
        assignSymbolic p TBool (offset + (fromInteger j)) v
    return Nothing
    
  SGateCall _ mods gid cs qs -> do
    cs'  <- mapM (evalExpr p) cs
    qs'  <- mapM (evalAP p) qs
    mod' <- evalModifiers mods
    gate <- generateGate gid cs'
    applyBlock p qs' (mod' gate)
    return Nothing
      
  SAnnotated _ annots stmt   -> simStmt p stmt

  SReturn _ (Just e)         -> liftM Just $ evalExpr p e
  SReturn _ Nothing          -> return $ Just VUnit
  SExpr _ expr               -> evalExpr p expr >> return Nothing
