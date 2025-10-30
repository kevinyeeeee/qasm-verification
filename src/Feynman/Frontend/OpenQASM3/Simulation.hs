module Feynman.Frontend.OpenQASM3.Simulation where

import Control.Monad.State.Strict
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import qualified Data.List as List
import Feynman.Algebra.Base (DMod2, DyadicRational, fromDyadic, toDyadic)
import Feynman.Algebra.SArith
import Feynman.Algebra.Pathsum.Balanced
import Feynman.Core (ID)
import Feynman.Frontend.OpenQASM3.Core
import Feynman.Frontend.OpenQASM3.TypeCheck (ElaboratedType(EType,ty), typeof)
import Feynman.Algebra.Polynomial.Multilinear (SBool, ofVar, rename, PseudoBoolean, cast, constant, canonicalize)
import Data.Bits (Bits, testBit, xor, (.&.))
import Data.Complex ( Complex, imagPart, realPart )

import qualified Feynman.Util.Unicode as U
import GHC.Real (reduce)
import Feynman.Frontend.OpenQASM3.Core (TypeExpr'(TCReg))
import Feynman.Algebra.SArith (sPopcount, sAnd, sXor, sLShift, sLRot)
import Control.Monad (forM)

import qualified Debug.Trace as Trace

isPowerOfTwo :: (Bits i, Integral i) => i -> Bool
isPowerOfTwo n = n > 0 && (n .&. (n - 1)) == 0

data Env = Env {
  pathsum :: Pathsum DMod2,
  binds :: [Map ID Binding],
  density :: Bool,
  qwidth :: Int                  -- number of allocated qubits
} deriving (Show)

data Binding =
    Symbolic { typ :: Type, offset :: Int }
  | Scalar { typ :: Type, value :: Value }
  | Block { typ :: Type, params :: [(ID, Type)], returns :: Maybe Type, body :: Stmt ElaboratedType }
  | Gate { typ :: Type, params :: [(ID, Type)], args :: [ID], body :: Stmt ElaboratedType }
  deriving (Show)

data Value =
    VInt Int
  | VPi
  | VIm
  | VBool Bool
  | VList [Value]
  | VFloat Double
  | VCmplx (Complex Double)
  | VQBit Int
  | VQReg Int Int -- offset, size
  | VCBit Int
  | VCReg Int Int
  | VPoly (SBool Var)
  | VPolyList [SBool Var]
  | VUnit
  deriving (Show)

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
  _ -> error $ show ty ++ " " ++ show val

offsetOfVal :: Value -> Int
offsetOfVal v = case v of
  VQBit n -> n
  _ -> error "no offset"

getPolyOfValue :: Value -> State Env (SBool Var)
getPolyOfValue v = case v of
  VBool True  -> return 1
  VBool False -> return 0
  VPoly p     -> return p
  VCBit j     -> getOutPoly j
  VInt  1     -> return 1
  VInt  0     -> return 0

typeExprToType :: TypeExpr ElaboratedType -> State Env Type
typeExprToType typ = case typ of
  TQBit -> return TQBit
  TBool -> return TBool
  TCReg e -> do
    v <- reduceExpr e
    case v of
      VInt n -> return $ TCReg n
  TQReg e -> do
    v <- reduceExpr e
    case v of
      VInt n -> return $ TQReg n
  TUInt (Just e) -> do
    v <- reduceExpr e
    case v of
      VInt n -> return $ TUInt (Just n)
  TUInt Nothing -> return $ TUInt Nothing
  TInt (Just e) -> do
    v <- reduceExpr e
    case v of
      VInt n -> return $ TInt (Just n)
  TInt Nothing -> return $ TInt Nothing
  TAngle (Just e) -> do
    v <- reduceExpr e
    case v of
      VInt n -> return $ TAngle (Just n)
  TFloat (Just e) -> do
    v <- reduceExpr e
    case v of
      VInt n -> return $ TFloat (Just n)
  TCmplx (Just e) -> do
    v <- reduceExpr e
    case v of
      VInt n -> return $ TCmplx (Just n)
  TUnit -> return TUnit
  TRange ts -> liftM TRange $ typeExprToType ts
  TGate {} -> error "todo"
  TProc {} -> error "todo"

getQWidth :: State Env Int
getQWidth = gets qwidth

getCWidth :: State Env Int
getCWidth = gets go
  where
    go (Env ps _ False qwidth) = outDeg ps - qwidth
    go (Env ps _ True  qwidth) = outDeg ps - 2*qwidth

offsetListOfPath :: AccessPath ElaboratedType -> State Env [Int]
offsetListOfPath path = case path of
  AVar _ vid -> do
    bind <- searchBinding vid
    case bind of
      Nothing -> error "bind not found"
      Just b  -> case b of
        Symbolic (TQReg n) offset -> return [ i | i <- [offset..offset+n-1] ] 
        Symbolic TQBit     offset -> return [ offset ]
  AIndex _ vid e -> do
    e' <- reduceExpr e
    case e' of
      VInt i -> do
        bind <- searchBinding vid
        case bind of
          Just b -> case b of
            Symbolic (TQReg n) offset -> return [offset + i]
          Nothing -> error "binding not found"
      _      -> error "index by non-int" 

-- | Gives the unicode representation of the ith offset of v
varOfOffset :: ID -> Int -> String
varOfOffset v i = U.sub v (fromIntegral i)

searchBinding :: ID -> State Env (Maybe Binding)
searchBinding id = gets $ search . binds
  where
    search []     = Nothing
    search (b:bs) = case Map.lookup id b of
      Just bind -> Just bind
      Nothing   -> search bs

addBinding :: ID -> Binding -> State Env ()
addBinding id bind = do
  env <- get
  let ~(b:bs) = binds env
  put $ env { binds = Map.insert id bind b : bs }

renameFVar :: Var -> Var
renameFVar v = case v of
  FVar s -> FVar $ "'" ++ s
  _      -> v

renameKet :: Pathsum DMod2 -> Pathsum DMod2
renameKet ps@(Pathsum _ _ _ _ p o) =
  ps { phasePoly = (rename renameFVar) p , outVals = map (rename renameFVar) o }

-- TODO: size redundant if list given. replace with Either?
allocateQBits :: ID -> Int -> Maybe [SBool String] -> State Env Int
allocateQBits v size init = do
  offset <- getQWidth
  modify $ allocateQ
  return $ offset 
  where
    qbits                              = case init of
      Nothing   -> ket [ofVar (varOfOffset v i) | i <- [0..size-1]]
      Just list -> ket list
    qbits'                             = case init of
      Nothing   -> renameKet $ ket [ofVar (varOfOffset v i) | i <- [0..size-1]]
      Just list -> renameKet (ket list)
    allocateQ env@(Env ps _ density w) = env { pathsum = newPs, qwidth = w + size }
      where
        psSize   = outDeg ps
        newOuts  = if density then qbits <> qbits' else qbits
        embedded = embed newOuts psSize (\i -> i) (\i -> if i < size then i + w else i + 2*w)
        newPs    = ps .> embedded

allocateQType :: ID -> Pathsum DMod2 -> State Env Int
allocateQType v qbits = do
  offset <- getQWidth
  modify $ allocateQ
  return $ offset 
  where
    qbits' = renameKet qbits
    size   = length (outVals qbits)
    allocateQ env@(Env ps _ density w) = env { pathsum = newPs, qwidth = w + size }
      where
        psSize   = outDeg ps
        newOuts  = if density then qbits <> (conjugate qbits') else qbits
        embedded = embed newOuts psSize (\i -> i) (\i -> if i < size then i + w else i + 2*w)
        newPs    = ps .> embedded

allocateCBits :: ID -> Int -> Maybe [SBool String] -> State Env Int
allocateCBits v size init = do
  offset <- getCWidth
  modify $ allocateC
  return $ offset 
  where
    bits                                 = case init of
      Nothing   -> ket $ [ofVar (varOfOffset v i) | i <- [0..size-1]]
      Just list -> ket $ list
    allocateC env@(Env ps _ density w) = env { pathsum = newPs }
      where
        psSize   = outDeg ps
        embedded = embed bits psSize (\i -> i) (\i -> i + psSize)
        newPs    = ps .> embedded

allocateCType :: ID -> Pathsum DMod2 -> State Env Int
allocateCType v bits = do
  offset <- getCWidth
  modify $ allocateC
  return $ offset 
  where
    allocateC env@(Env ps _ density w) = env { pathsum = newPs }
      where
        psSize   = outDeg ps
        embedded = embed bits psSize (\i -> i) (\i -> i + psSize)
        newPs    = ps .> embedded

measurePS :: Int -> Env -> Env
measurePS _      env@(Env _ _ False _)      = error "not density matrix"
measurePS offset env@(Env ps _ True qwidth) = env { pathsum = ps' }
  where
    ps' = applyMeasure offset (offset + qwidth) ps

bindParams :: [(ID, Type)] -> [Value] -> State Env ()
bindParams params args = mapM_ bindParam $ zip params args

bindParam :: ((ID, Type), Value) -> State Env ()
bindParam ((pid, ptype), v) = case (ptype, v) of
  (TQBit  , VQBit o  )   -> addBinding pid $ Symbolic TQBit o 
  (TBool  , VCBit o  )   -> addBinding pid $ Symbolic TBool o
  (TQReg n, VQReg o m)   -> if m == n then addBinding pid $ Symbolic (TQReg n) o else error "type mismatch"
  (TCReg n, VCReg o m) -> addBinding pid $ Symbolic (TCReg n) o
  (TUInt (Just n), VCReg o m) -> addBinding pid $ Symbolic (TUInt $ Just n) o
  (_, _)                 ->
    addBinding pid $ Scalar ptype v

initEnv :: Bool -> Env
initEnv b = Env (ket []) [Map.empty] b 0

pushEmptyEnv :: State Env ()
pushEmptyEnv =
  modify $ \env -> env { binds = Map.empty : binds env }

popEnv :: State Env ()
popEnv =
  modify $ \env -> env { binds = tail $ binds env }

reduceExpr :: Expr ElaboratedType -> State Env Value
reduceExpr expr = case expr of
  EInt _ n     -> return $ VInt n
  EFloat _ f   -> return $ VFloat f 
  ECmplx _ c   -> return $ VCmplx c
  EBool _ b    -> return $ VBool b 
  EPi _        -> return VPi
  EIm _        -> return VIm
  EBits _ bs   -> return $ VPolyList (map (\b -> if b then 1 else 0) bs)
  ECast t _ e  -> do
    v <- reduceExpr e
    return $ castValue t v
  EMeasure _ e -> do
    v <- reduceExpr e
    case v of
      VQBit i      -> do
        modify $ measurePS i
        gets $ \env -> VPoly . (!! i) . outVals $ pathsum env
      VQReg i size -> liftM VPolyList $
        forM [i..i+size-1] ( \j -> do
          modify $ measurePS j
          gets $ \env -> (!! j) . outVals $ pathsum env )
  EVar _ vid   -> do
    bind <- searchBinding vid
    case bind of
      Nothing                    -> error "binding not found"
      Just (Scalar _ e)          -> return e
      Just (Symbolic typ offset) -> case typ of
        TCReg n -> return $ VCReg offset n
        TBool   -> return $ VCBit offset
        TQBit   -> return $ VQBit offset
        TQReg n -> return $ VQReg offset n
        TUInt (Just n) -> return $ VCReg offset n
        _       -> error "invalid symbolic type"
  EIndex _ x i -> do
    x' <- reduceExpr x
    i' <- reduceExpr i
    case (x', i') of
      (VPolyList l      , VInt i) -> return $ VPoly (l !! i)
      (VQReg offset size, VInt i) -> if i < size then return $ VQBit (offset + i) else error "index out of range"
      (VCReg offset size, VInt i) -> if i < size then return $ VCBit (offset + i) else error "index out of range"
      (VList l          , VInt i) -> return $ l !! i
      _                       -> error "non indexable expression"
  ESet _ l    -> do
    set <- mapM reduceExpr l
    return $ VList set
--slicing inclusive on both ends
  ESlice _ start step stop -> do
    n <- reduceExpr start
    m <- reduceExpr stop
    case (n, m) of
      (VInt start', VInt stop') -> case step of
        Just s -> do
          l <- reduceExpr s
          case l of
            VInt step' -> return $ VList [ VInt j | i <- [start'..stop'],
                                                    let j = i * step',
                                                    j <= stop' ]
        Nothing -> return $ VList [ VInt i | i <- [start'..stop'] ]
  EUOp _ uop a -> do
    v <- reduceExpr a
    case (uop, v) of
      (SinOp     , VFloat f   ) -> return $ VFloat $ sin f
      (CosOp     , VFloat f   ) -> return $ VFloat $ cos f
      (TanOp     , VFloat f   ) -> return $ VFloat $ tan f
      (ArccosOp  , VFloat f   ) -> return $ VFloat $ acos f
      (ArcsinOp  , VFloat f   ) -> return $ VFloat $ asin f
      (ArctanOp  , VFloat f   ) -> return $ VFloat $ atan f
      (CeilOp    , VFloat f   ) -> return $ VInt $ ceiling f
      (FloorOp   , VFloat f   ) -> return $ VInt $ floor f
      (LnOp      , VFloat f   ) -> return $ VFloat $ log f --maybe need to check base
      (RealOp    , VCmplx c   ) -> return $ VFloat $ realPart c
      (ImOp      , VCmplx c   ) -> return $ VFloat $ imagPart c
      (NegOp     , VBool b    ) -> return $ VBool $ not b
      (NegOp     , VPolyList l) -> return $ VPolyList $ sNot l
      (NegOp     , VPoly p    ) -> return $ VPoly $ head (sNot [p])
      (UMinusOp  , VPolyList l) -> return $ VPolyList $ sNeg l
      (PopcountOp, VPolyList l) -> return $ VPolyList $ sPopcount l
      _  -> error "error in uop expr reduction"
  EBOp t a bop b -> do
    v1 <- reduceExpr a
    v2 <- reduceExpr b
    case (bop, v1, v2) of
      (AndOp   , VBool b1 , VBool b2 ) -> return $ VBool $ b1 && b2
      (OrOp    , VBool b1 , VBool b2 ) -> return $ VBool $ b1 || b2
      (XorOp   , VBool b1 , VBool b2 ) -> return $ VBool $ b1 `xor` b2
--      (LShiftOp, _        , _        ) -> error "check: should work like rotl?"
--      (RShiftOp, _        , _        ) -> error "check: should work like rotr?"
      (EqOp    , VBool b1 , VBool b2 ) -> return $ VBool $ b1 == b2
      (EqOp    , VInt i1  , VInt i2  ) -> return $ VBool $ i1 == i2
      (EqOp    , VFloat f1, VFloat f2) -> return $ VBool $ f1 == f2
      (EqOp    , VCmplx c1, VCmplx c2) -> return $ VBool $ c1 == c2
--      (EqOp    , _        , _        ) -> error "constraint propagation? ex uint = int"
      (LTOp    , VInt i1  , VInt i2  ) -> return $ VBool $ i1 < i2
      (LTOp    , VFloat f1, VFloat f2) -> return $ VBool $ f1 < f2
      (LEqOp   , VInt i1  , VInt i2  ) -> return $ VBool $ i1 <= i2
      (LEqOp   , VFloat f1, VFloat f2) -> return $ VBool $ f1 <= f2
      (GTOp    , VInt i1  , VInt i2  ) -> return $ VBool $ i1 > i2
      (GTOp    , VFloat f1, VFloat f2) -> return $ VBool $ f1 > f2
      (GEqOp   , VInt i1  , VInt i2  ) -> return $ VBool $ i1 >= i2
      (GEqOp   , VFloat f1, VFloat f2) -> return $ VBool $ f1 >= f2
      (PlusOp  , VInt i1  , VInt i2  ) -> return $ VInt $ i1 + i2
      (PlusOp  , VFloat f1, VFloat f2) -> return $ VFloat $ f1 + f2
      (PlusOp  , VCmplx c1, VCmplx c2) -> return $ VCmplx $ c1 + c2
      (MinusOp , VInt i1  , VInt i2  ) -> return $ VInt $ i1 - i2
      (MinusOp , VFloat f1, VFloat f2) -> return $ VFloat $ f1 - f2
      (MinusOp , VCmplx c1, VCmplx c2) -> return $ VCmplx $ c1 - c2
      (TimesOp , VInt i1  , VInt i2  ) -> return $ VInt $ i1 * i2
      (TimesOp , VFloat f1, VFloat f2) -> return $ VFloat $ f1 * f2
      (TimesOp , VCmplx c1, VCmplx c2) -> return $ VCmplx $ c1 * c2 -- need to implement casting
      (DivOp   , VInt i1  , VInt i2  ) -> return $ VInt $ i1 `quot` i2 -- div?
      (DivOp   , VFloat f1, VFloat f2) -> return $ VFloat $ f1 / f2
      (DivOp   , VCmplx c1, VCmplx c2) -> return $ VCmplx $ c1 / c2
      (ModOp   , VInt i1  , VInt i2  ) -> return $ VInt $ i1 `mod` i2
      (PowOp   , VInt i1  , VInt i2  ) -> return $ VInt $ i1 ^ i2
      (AndOp   , VPolyList l1, VPolyList l2) -> return $ VPolyList (sAnd l1 l2)
      (OrOp    , VPolyList l1, VPolyList l2) -> return $ VPolyList (sOr l1 l2)
      (XorOp   , VPolyList l1, VPolyList l2) -> return $ VPolyList (sXor l1 l2)
      (LShiftOp, VPolyList l1, VPolyList l2) -> return $ VPolyList (sLShift l1 l2)
      (RShiftOp, VPolyList l1, VPolyList l2) -> return $ VPolyList (sRShift l1 l2)
      (LRotOp  , VPolyList l1, VPolyList l2) -> return $ VPolyList (sLRot l1 l2)
      (RRotOp  , VPolyList l1, VPolyList l2) -> return $ VPolyList (sRRot l1 l2)
      (PlusOp  , VPolyList l1, VPolyList l2) -> return $ VPolyList (sPlus l1 l2)
      (MinusOp , VPolyList l1, VPolyList l2) -> return $ VPolyList (sMinus l1 l2)
      (TimesOp , VPolyList l1, VPolyList l2) -> return $ VPolyList (sMult l1 l2)
      (DivOp   , VPolyList l1, VPolyList l2) -> return $ VPolyList (sQuot l1 l2)
      (ModOp   , VPolyList l1, VPolyList l2) -> return $ VPolyList (sMod l1 l2)
      (PowOp   , VPolyList l1, VPolyList l2) -> return $ VPolyList (sPow l1 l2)
      (EqOp    , VPolyList l1, VPolyList l2) -> return $ VPoly (sEq l1 l2)
      (LTOp    , VPolyList l1, VPolyList l2) -> return $ VPoly (sLT l1 l2)
      (LEqOp   , VPolyList l1, VPolyList l2) -> return $ VPoly (sLEq l1 l2)
      (GTOp    , VPolyList l1, VPolyList l2) -> return $ VPoly (sGT l1 l2)
      (GEqOp   , VPolyList l1, VPolyList l2) -> return $ VPoly (sGEq l1 l2)
      (EqOp    , VPoly p1    , VPoly p2    ) -> return $ VPoly (sEq [p1] [p2])
      (AndOp   , VPoly p1    , VPoly p2    ) -> return $ VPoly $ head (sAnd [p1] [p2])
      (OrOp    , VPoly p1    , VPoly p2    ) -> return $ VPoly $ head (sOr [p1] [p2])
      (XorOp   , VPoly p1    , VPoly p2    ) -> return $ VPoly $ head (sXor [p1] [p2])
      (EqOp    , VCBit _     , _           ) -> do
        p1 <- getPolyOfValue v1
        p2 <- getPolyOfValue v2
        return $ VPoly (sEq [p1] [p2])
      _ -> error $ show a ++ show bop ++ show b ++ "  type:" ++ show t
  _ -> error "todo?"
      
simStmt :: SBool Var -> Stmt ElaboratedType -> State Env (Maybe Value)
simStmt p stmt = case stmt of
  SSkip _                    -> return Nothing
  SBarrier _ _               -> return Nothing
  SPragma _ _                -> return Nothing
  SBlock _ stmts             -> simBlock p stmts
  SWhile _ cond stmt         -> simWhile p cond stmt
  SIf _ cond stmtT stmtE     -> simIf p cond stmtT stmtE
  
  SReset _ expr              -> simReset expr >> return Nothing
  SDeclare _ decl            -> if p == 1 then
                                  simDeclare decl >> return Nothing
                                else
                                  error "invalid stmt in symbolic branch"
  SAssign _ path expr        -> simAssign p path expr >> return Nothing
  SGateCall _ mods gid cpars qargs -> simGate p gid mods cpars qargs >> return Nothing

  SAnnotated _ annots stmt   -> simAnnotated p annots stmt
  SFor _ (id, typ) expr stmt -> simFor p (id, typ) expr stmt
  SReturn _ (Just e)         -> liftM Just $ reduceExpr e
  SReturn _ Nothing          -> return $ Just VUnit
  SExpr _ expr               -> simExpr p expr >> return Nothing

simAnnotated :: SBool Var -> [Annotation ElaboratedType] -> Stmt ElaboratedType -> State Env (Maybe Value)
simAnnotated p annots stmt = case stmt of
  SDeclare _ decl@(DDef _ params _ body) -> do
    verifyDef pre post params body
    simDeclare decl
    return Nothing
  SDeclare _ decl@(DGate _ params qargs body) -> do
    verifyDef pre post (params ++ zip qargs (repeat TQBit)) body
    simDeclare decl
    return Nothing
  _               -> simStmt p stmt
  where
    (pre, post) = case List.find (\a -> case a of
      Triple _ _ -> True
      _          -> False ) annots of
        Just (Triple pre post) -> (pre, post)
        _                      -> ([] , []  )

verifyAssert :: [(AccessPath a, Expr a)] -> State Env ()
verifyAssert conds = error "TODO"

verifyDef :: [(AccessPath ElaboratedType, Expr ElaboratedType)] -> [(AccessPath ElaboratedType, Expr ElaboratedType)] -> [(ID, TypeExpr ElaboratedType)] -> Stmt ElaboratedType -> State Env ()
verifyDef pre post binds body = do
  binds' <- traverse (\(a, x) -> (,) a <$> typeExprToType x) binds
  preState <- setUpPre binds'
  let env = execState (simStmt 1 body) preState
  if checkPost binds' env then
    return ()
  else
    error "verification failed"
  where
    checkPost binds (Env ps _ _ _) =
      let (Env ps' _ _ _) = execState (g post binds) (initEnv True) in
        error $ show ps ++ "   " ++ show ps'
    setUpPre binds = return $ execState (g pre binds) (initEnv True)
    g conds binds    = forM binds (\(id, typ) -> do
      initKet <- y conds (id, typ)
      declareWithPS id typ initKet )

    y :: [(AccessPath ElaboratedType, Expr ElaboratedType)] -> (ID, Type) -> State Env (Pathsum DMod2)
    y conds (aid, typ) = case List.find ( \(a, _) -> case a of
                                          AVar _ id -> aid == id
                                          AIndex _ id _ -> aid == id ) conds of
      Just (_, e) -> simKet e
      Nothing     -> case typ of
        TQBit   -> return $ ket [ ofVar aid ]
        TBool   -> return $ ket [ ofVar aid ]
        TQReg n -> do
            psList <- mapM (yy conds) [ ((aid, i), TQBit) | i <- [0..n-1] ]
            return $ foldr1 (<>) psList
        TCReg n -> do
            psList <- mapM (yy conds) [ ((aid, i), TBool) | i <- [0..n-1] ]
            return $ foldr1 (<>) psList
        TUInt (Just n) -> do
            psList <- mapM (yy conds) [ ((aid, i), TBool) | i <- [0..n-1] ]
            return $ foldr1 (<>) psList

    yy conds ((aid, i), typ) = case List.find ( \(a, _) -> case a of
                                                AVar _ _ -> False
                                                AIndex _ id (EInt _ j) -> aid == id && i == j ) conds of
      Just (_, e) -> simKet e
      Nothing     -> case typ of
        TQBit -> return $ ket [ ofVar (varOfOffset aid i) ]
        TBool -> return $ ket [ ofVar (varOfOffset aid i) ]

simKet :: Expr ElaboratedType -> State Env (Pathsum DMod2)
simKet expr = case expr of
  Tensor _ e1 e2          -> liftM2 (<>) (simKet e1) (simKet e2)
  Sum _ svars e           -> do
    ps <- simKet e
    let (ids, typs) = unzip svars
    typs <- mapM (traverse $ typeExprToType) typs
    let svars = zip ids typs 
    return $ sumOver svars ps
  EUOp _ ExpOp e          -> do
    pp <- exprToPhasePoly e
    return $ Pathsum 0 0 0 0 pp []
  Ket _ (EVar vtyp vid) -> do
    case ty vtyp of
      TBool          -> return $ ket [ ofVar vid ]
      TCReg n        -> return $ ket [ ofVar (varOfOffset vid i) | i <- [0..n-1] ]
      TUInt (Just m) -> return $ ket [ ofVar (varOfOffset vid i) | i <- [0..m-1] ]
  Ket _ e                 -> liftM (ket . (\a -> [a])) (exprToBoolPoly e)
  EBOp _ e1 PlusOp e2 -> do
    ps1 <- simKet e1
    ps2 <- simKet e2
    return $ plus ps1 ps2
  EBOp _ e1 TimesOp e2 -> liftM2 (<>) (simKet e1) (simKet e2)

exprToDyadicPoly :: Expr ElaboratedType -> State Env (PseudoBoolean Var DyadicRational)
exprToDyadicPoly e = case e of
  EBOp _ divi DivOp (EInt _ n) -> 
    if isPowerOfTwo n then
      do
        pp <- exprToDyadicPoly divi
        return $ pp * constant (toDyadic $ 1.0 / fromIntegral n)
    else error "phase poly not dyadic"
  EBOp _ e1 TimesOp e2       -> do
    pp1 <- exprToDyadicPoly e1
    pp2 <- exprToDyadicPoly e2
    return $ pp1 * pp2
  EBOp _ e1 PlusOp e2        -> do
    pp1 <- exprToDyadicPoly e1
    pp2 <- exprToDyadicPoly e2
    return $ pp1 + pp2
  EBOp _ e1 MinusOp e2       -> do
    pp1 <- exprToDyadicPoly e1
    pp2 <- exprToDyadicPoly e2
    return $ pp1 - pp2
  EInt _ n                   -> return $ fromInteger $ toInteger n
  EVar vtyp vid              -> case ty vtyp of
    TBool          -> return $ ofVar (FVar vid)
    TUInt (Just n) -> return $ bitBlast n vid
  where
    bitBlast m id = foldl1 (+) [ (2 ^ i) * ofVar (FVar $ varOfOffset id i) | i <- [0..m-1] ]

exprToPhasePoly :: Expr ElaboratedType -> State Env (PseudoBoolean Var DMod2)
exprToPhasePoly = liftM (cast fromDyadic) . exprToDyadicPoly

exprToBoolPoly :: Expr ElaboratedType -> State Env (SBool String)
exprToBoolPoly e = case e of
  EInt _ 0 -> return 0
  EInt _ 1 -> return 1
  EBool _ False -> return 0
  EBool _ True  -> return 1
  EVar _ vid -> return $ ofVar vid
  EBOp _ e1 TimesOp e2 -> do
    p1 <- exprToBoolPoly e1
    p2 <- exprToBoolPoly e2
    return $ p1 * p2
  EBOp _ e1 PlusOp e2  -> do
    p1 <- exprToBoolPoly e1
    p2 <- exprToBoolPoly e2
    return $ p1 + p2

sumOver :: [(ID, Maybe Type)] -> Pathsum DMod2 -> Pathsum DMod2
sumOver svars = sumover (concatMap go svars) where
  go (vid, Nothing)               = [vid]
  go (vid, Just TBool)            = [vid]
  go (vid, Just (TUInt (Just n))) = [varOfOffset vid i | i <- [0..n-1]]

simBlock :: SBool Var -> [Stmt ElaboratedType] -> State Env (Maybe Value)
simBlock p = foldM f Nothing
  where
    f (Just r) _    = return $ Just r
    f Nothing  stmt = simStmt p stmt

simWhile :: SBool Var -> Expr ElaboratedType -> Stmt ElaboratedType -> State Env (Maybe Value)
simWhile p cond stmt = do
  v <- reduceExpr cond --symbolic branching?
  case v of
    VBool b ->
      if b then
        ( do
            ret <- simStmt p stmt
            case ret of
              Nothing -> simWhile p cond stmt
              Just v  -> return $ Just v )
      else
        return Nothing

simIf :: SBool Var -> Expr ElaboratedType -> Stmt ElaboratedType -> Stmt ElaboratedType -> State Env (Maybe Value)
simIf p cond stmtT stmtE = do
  cond' <- reduceExpr cond
  case cond' of
    VBool True  -> simStmt p stmtT
    VBool False -> simStmt p stmtE
    VPoly q     -> do
      simStmt (p*q) stmtT
      simStmt (p*(1+q)) stmtE

simFor :: SBool Var -> (ID, TypeExpr ElaboratedType) -> Expr ElaboratedType -> Stmt ElaboratedType -> State Env (Maybe Value)
simFor p (id, typExpr) expr stmt = do
  v <- reduceExpr expr
  ty <- typeExprToType typExpr
  case v of
    VList list ->
      foldM iter Nothing list
      where
        iter (Just r) _ = return $ Just r
        iter Nothing  e = do
          pushEmptyEnv
          bindParam ((id, ty), e)
          ret <- simStmt p stmt
          popEnv
          return ret 

listOpOfBOp :: BinOp -> [SBool Var] -> [SBool Var] -> [SBool Var]
listOpOfBOp bop = case bop of
  AndOp    -> sAnd
  OrOp     -> sOr
  XorOp    -> sXor
  LShiftOp -> sLShift
  RShiftOp -> sRShift
  LRotOp   -> sLRot
  RRotOp   -> sRRot
  PlusOp   -> sPlus
  MinusOp  -> sMinus
  TimesOp  -> sMult 
  DivOp    -> sQuot
  ModOp    -> sMod
  PowOp    -> sPow
  ConcatOp -> error "++ not supported"
  _        -> error "given bop does not output list of polynomials"

boolOpOfBop :: BinOp -> [SBool Var] -> [SBool Var] -> SBool Var
boolOpOfBop bop = case bop of
  EqOp  -> sEq
  LTOp  -> sLT 
  LEqOp -> sLEq
  GTOp  -> sGT
  GEqOp -> sGEq
  _     -> error "given bop does not output boolean polynomial"

listOpOfUop :: UOp -> [SBool Var] -> [SBool Var]
listOpOfUop uop = case uop of
  NegOp      -> sNot
  UMinusOp   -> sNeg
  PopcountOp -> sPopcount
  _        -> error "given uop does not output list of polynomials"

simAssign :: SBool Var -> AccessPath ElaboratedType -> Expr ElaboratedType -> State Env ()
simAssign p path expr = case path of
  AVar _ id     -> do
    maybeBind <- searchBinding id
    case maybeBind of
      Nothing                    -> error "id not bound"
      Just (Scalar typ _)        -> if p == 1 then do
                                      declareScalar id typ (Just $ expr)
                                    else
                                      error "bad symbolic branching" 
      Just (Symbolic typ offset) -> simSymbolicAssign p offset typ expr
  AIndex _ id i -> do
    maybeBind <- searchBinding id
    i' <- reduceExpr i
    case i' of
      VInt j ->
        case maybeBind of
          Nothing                    -> error "id not bound"
          Just (Scalar typ e)        -> error "not sure if allowed"
          Just (Symbolic typ offset) -> simSymbolicAssign p (offset + j) TBool expr
      _ -> error "index is not an int value"

simSymbolicAssign :: SBool Var -> Int -> Type -> Expr ElaboratedType -> State Env ()
simSymbolicAssign p offset typ expr = do
  v <- reduceExpr expr
  case (typ, v) of
    (TBool  , VPoly poly ) -> modify $ f [poly]
    (TBool  , VBool False) -> modify $ f [0]
    (TBool  , VBool True ) -> modify $ f [1]
    (TCReg n, VPolyList l) -> modify $ f l 
    (TUInt n, VPolyList l) -> modify $ f l
  where
    f polyl env@(Env ps@(Pathsum _ _ _ _ _ out) _ density qwidth) =
      let n            = length polyl
          (qreg, creg) = splitAt (if density then 2*qwidth else qwidth) out
          oldList      = drop offset . take (offset + n) $ creg
          newList      = zipWith (\old new -> p*new + (1+p)*old) oldList polyl
          newCreg      = take offset creg ++ newList ++ drop (offset + n) creg in
        env { pathsum = ps { outVals = qreg ++ newCreg } }

getOutPoly :: Int -> State Env (SBool Var)
getOutPoly = gets . g
  where
    g j (Env (Pathsum _ _ _ _ _ out) _ False qwidth) = out !! (j + qwidth)
    g j (Env (Pathsum _ _ _ _ _ out) _ True  qwidth) = out !! (j + 2*qwidth)

getOutPolyList :: [Int] -> State Env [SBool Var]
getOutPolyList = mapM getOutPoly

declareWithPS :: ID -> Type -> Pathsum DMod2 -> State Env ()
declareWithPS id typ ps = do
  offset <- f id ps
  addBinding id (Symbolic typ offset )
  where
    f = case typ of
      TBool   -> allocateCType
      TCReg _ -> allocateCType
      TUInt _ -> allocateCType
      TQBit   -> allocateQType
      TQReg _ -> allocateQType

declareSymbolic :: ID -> Type -> Int -> Maybe [SBool String] -> State Env ()
declareSymbolic id typ size init = declareWithPS id typ ps
  where
    ps = case init of
      Just s -> ket s
      Nothing -> case typ of
        TBool   -> ket [ofVar id]
        TQBit   -> ket [ofVar id]
        TCReg _ -> ket [ofVar (varOfOffset id i) | i <- [0..size-1]]
        TUInt _ -> ket [ofVar (varOfOffset id i) | i <- [0..size-1]]
        TQReg _ -> ket [ofVar (varOfOffset id i) | i <- [0..size-1]]

declareScalar :: ID -> Type -> Maybe (Expr ElaboratedType) -> State Env ()
declareScalar id typ maybeExpr = do
  val <- getValueOrDefault
  addBinding id (Scalar typ val)
  where
    getValueOrDefault = case maybeExpr of
      Just e  -> reduceExpr e            -- eval first?
      Nothing -> return $ case typ of
        TAngle _ -> VFloat 0 
        TBool    -> VBool False -- true?
        TInt   _ -> VInt 0
        TFloat _ -> VFloat 0
        TCmplx _ -> VCmplx 0

declareBlock :: ID -> [(ID, Type)] -> Maybe Type -> Stmt ElaboratedType -> State Env ()
declareBlock id params returns body = let (_, sig) = unzip params in
  addBinding id (Block (TProc sig returns) params returns body)

declareGate :: ID -> [(ID, Type)] -> [ID] -> Stmt ElaboratedType -> State Env ()
declareGate id params qargs body =
  addBinding id (Gate (TGate (length params) (length qargs)) params qargs body)

simDeclare :: Decl ElaboratedType -> State Env ()
simDeclare decl = case decl of
  DVar vid typ maybeExpr const -> case typ of
    TBool   -> case maybeExpr of
      Nothing -> declareSymbolic vid TBool 1 Nothing
      Just e  -> do 
        v <- reduceExpr e
        case v of
          VBool False -> declareSymbolic vid TBool 1 (Just [0])
          VBool True  -> declareSymbolic vid TBool 1 (Just [1])
    TCReg n -> do
      n' <- reduceExpr n
      case n' of
        VInt size -> case maybeExpr of
          Nothing       -> declareSymbolic vid (TCReg size) size Nothing
          Just e        -> do 
            v <- reduceExpr e
            case v of
              VInt j -> declareSymbolic vid (TCReg size) size (Just $ bitVec j size)
        _   -> error $ "invalid register size"
    TQBit   -> case maybeExpr of
      Nothing -> declareSymbolic vid TQBit 1 Nothing
      Just _  -> error $ "invalid value in qubit declaration"
    TQReg n -> do
      n' <- reduceExpr n
      case n' of
        VInt size -> case maybeExpr of
          Nothing -> declareSymbolic vid (TQReg size) size Nothing
          Just _  -> error $ "invalid qreg value"
        _         -> error $ "invalid register size"
    TUInt (Just n) -> do
      n' <- reduceExpr n
      case n' of
        VInt size -> case maybeExpr of
          Nothing       -> declareSymbolic vid (TUInt $ Just size) size Nothing
          Just e        -> do 
            v <- reduceExpr e
            case v of
              VInt j -> declareSymbolic vid (TUInt $ Just size) size (Just $ bitVec j size)
        _   -> error $ "invalid register size"
    typ -> do
      newtyp <- typeExprToType typ
      declareScalar vid newtyp maybeExpr
  DDef did dparams dreturns dbody -> do
    dreturns' <- mapM typeExprToType dreturns
    dparams' <- traverse (\(a, x) -> (,) a <$> typeExprToType x) dparams
    declareBlock did dparams' dreturns' dbody
  DGate gid gparams gqargs gbody -> do
    gparams' <- traverse (\(a, x) -> (,) a <$> typeExprToType x) gparams
    declareGate gid gparams' gqargs gbody
  DExtern _ _ _ -> error "TODO"
  DAlias  _ _   -> error "TODO"

bitVec :: Int -> Int -> [SBool String]
bitVec n size = map f [0..size-1]
  where
    f i = if testBit n i then 1 else 0

stdlib = ["x", "y", "z", "h", "cx", "cy", "cz", "ch", "id", "s", "sdg", "t", "tdg", "rz", "rx", "ry", "ccx", "crz", "u3", "u2", "u1", "cu1", "cu3", "swap"]

applyPS :: Pathsum DMod2 -> SBool Var -> [Int] -> State Env ()
applyPS gatePS p offsets = modify $ f
  where
    f env@(Env ps _ False _) = env { pathsum = applyPControlled gatePS p offsets ps }
    f env@(Env ps _ True qwidth) = 
      let offsets' = map (+qwidth) offsets in
        env { pathsum = applyPControlled (conjugate gatePS) p offsets' . applyPControlled gatePS p offsets $ ps }

applyModifiers :: Pathsum DMod2 -> [Modifier ElaboratedType] -> State Env (Pathsum DMod2)
applyModifiers = foldM applyModifier

applyModifier :: Pathsum DMod2 -> Modifier ElaboratedType -> State Env (Pathsum DMod2)
applyModifier ps mod = case mod of
  MCtrl _ False Nothing -> return $ controlled ps
  MCtrl _ False (Just expr) -> do
    e <- reduceExpr expr
    case e of
      VInt n -> return $ iterate controlled ps !! n

simGate :: SBool Var -> ID -> [Modifier ElaboratedType] -> [Expr ElaboratedType] -> [AccessPath ElaboratedType] -> State Env ()
simGate p gid mods cpars qargs
  | gid `elem` stdlib     = simStdGate p gid mods cpars qargs
  | otherwise             = error "TODO"

simStdGate :: SBool Var -> ID -> [Modifier ElaboratedType] -> [Expr ElaboratedType] -> [AccessPath ElaboratedType] -> State Env ()
simStdGate p gid mods cparams qargs = do
  gatePS <- getGatePS gid cparams
  gatePS <- applyModifiers gatePS mods
  vals <- mapM reduceExpr (map exprFromAP qargs)
  let offsets = map offsetOfVal vals
  applyPS gatePS p offsets

simExpr :: SBool Var -> Expr ElaboratedType -> State Env (Maybe Value)
simExpr p (EStmt _ stmt) = simStmt p stmt
    
simExpr p (ECall _ fid args) = do
  bind <- searchBinding fid
  args' <- (liftM $ map fromJust) $ mapM (simExpr p) args
  case bind of
    Just (Block _ params _ body) -> do
      pushEmptyEnv
      bindParams params args'
      ret <- simStmt p body
      popEnv
      return ret
    Nothing                      -> error "binding not found"

simExpr p expr = liftM Just $ reduceExpr expr

getGatePS :: ID -> [Expr ElaboratedType] -> State Env (Pathsum DMod2)
getGatePS id params = case (id, params) of
  ("x", [])   -> return $ xgate
  ("y", [])   -> return $ ygate
  ("z", [])   -> return $ zgate
  ("h", [])   -> return $ hgate
  ("cx", [])  -> return $ cxgate
  ("cy", [])  -> return $ controlled ygate
  ("cz", [])  -> return $ czgate
  ("ch", [])  -> return $ controlled hgate 
  ("id", [])  -> return $ identity 1
  ("s", [])   -> return $ sgate
  ("sdg", []) -> return $ sdggate
  ("t", [])   -> return $ tgate
  ("tdg", []) -> return $ tdggate
  ("ccx", []) -> return $ ccxgate
  ("swap", []) -> return $ swapgate
  _           -> error "TODO"

simReset :: Expr ElaboratedType -> State Env ()
simReset expr = case expr of
  EVar _ id -> do
    bind <- searchBinding id
    case bind of
      Nothing -> return ()
      Just (Symbolic TQBit offset)     -> modify $ resetOffset offset
      Just (Symbolic (TQReg n) offset) -> mapM_ modify [resetOffset i | i <- [offset..offset+n-1] ] 
  where
    resetOffset offset env@(Env ps@(Pathsum _ _ _ _ _ out) _ False _)     =
      env { pathsum = resetPS offset ps }
    resetOffset offset env@(Env ps@(Pathsum _ _ _ _ _ out) _ True qwidth) =
      env { pathsum = resetPS (offset + qwidth) . resetPS offset $ ps }

    resetPS offset ps@(Pathsum _ _ _ _ _ out) = ps { outVals = newOut }
      where
        newOut = take offset out ++ [0] ++ drop (offset + 1) out 

tracePaths :: [AccessPath ElaboratedType] -> State Env (Pathsum DMod2)
tracePaths paths = do
  offsets <- liftM concat $ mapM offsetListOfPath paths
  let sorted = reverse . List.sort $ offsets
  qwidth <- getQWidth
  ps <- gets $ pathsum
  return $ snd $ foldr go (qwidth, ps) offsets
  where
    go i (w, ps) = let ps' = traceOut i (i+w) ps in
      (w-1, ps') 

traceExcept :: [AccessPath ElaboratedType] -> State Env (Pathsum DMod2)
traceExcept paths = do
  offsets <- liftM concat $ mapM offsetListOfPath paths
  qwidth <- getQWidth
  ps <- gets $ pathsum
  return $ snd $ foldr (go offsets) (qwidth, ps) (reverse [0..qwidth-1])
  where
    go skips i (w, ps) = if i `elem` skips then
        (w, ps)
      else
        let ps' = traceOut i (i+w) ps in
          (w-1, ps')

simStmts :: [Stmt ElaboratedType] -> State Env ()
simStmts = mapM_ $ simStmt 1

simProgPure :: Prog ElaboratedType -> Env
simProgPure (Prog _ stmts) = execState (simStmts stmts) (initEnv False)

simProg :: Prog ElaboratedType -> Env
simProg (Prog _ stmts) = execState (simStmts stmts) (initEnv True)

simulationResult :: Prog ElaboratedType -> String
simulationResult prog = 
  let env = simProg prog in
    show (grind $ pathsum env)   
       
