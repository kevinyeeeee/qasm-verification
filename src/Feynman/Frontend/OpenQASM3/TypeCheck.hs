{-|
Module      : TypeCheck
Description : Type checker
Copyright   : (c) Matthew Amy, 2025
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Frontend.OpenQASM3.TypeCheck where

import Control.Monad
import Control.Monad.State

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (isJust, fromJust, fromMaybe)
import Data.Bits

import Feynman.Core (ID)
import qualified Feynman.Frontend.OpenQASM3.Syntax as S
import Feynman.Frontend.OpenQASM3.Core

{- Types -}

{- Basically duplicated type, but with a "top" type -}
data TypeConstraints = 
    ConsCReg Integer
  | ConsQBit
  | ConsQReg Integer
  | ConsBool 
  | ConsUInt (Maybe Integer)
  | ConsInt (Maybe Integer)
  | ConsAngle (Maybe Integer)
  | ConsFloat (Maybe Integer)
  | ConsCmplx (Maybe Integer)
  | ConsUnit
  | ConsRange TypeConstraints
  | ConsGate { numCargs :: Int, numQargs :: Int }
  | ConsProc { argTypes :: [TypeConstraints], returnType :: Maybe TypeConstraints }
  | ConsTop
  deriving (Show)

-- | Type elaborate with compile-time constant declarations
data ElaboratedType = EType { ty :: Type,
                              isConstant :: Bool,
                              -- Int constants, the only constants needed
                              -- for type checking
                              value :: Maybe Integer
                            } deriving (Show)

-- | Insert a type into an elaborated type
pureType :: Type -> ElaboratedType
pureType ty = EType ty False Nothing

-- | Insert a constant type into an elaborated type
constType :: Type -> ElaboratedType
constType ty = EType ty True Nothing

-- | Insert a constant type into an elaborated type
constInt :: Type -> Integer -> ElaboratedType
constInt ty i = EType ty True (Just i)

-- | Gets the base type of an AST node annotated with an elaborated type
typeof :: Annotated f => f ElaboratedType -> Type
typeof = ty . getAnnotation

-- | Instance for asTypeExpr specialized to type checking
asTypeExpr' :: Type -> TypeExpr ElaboratedType
asTypeExpr' = asTypeExpr (pureType $ TUInt Nothing)

-- | Type checking environment, consisting of bindings to
--   elaborate types and a list of error messages
data Env = Env { scopes :: [Map ID ElaboratedType],
                 errs  :: [ErrMsg],
                 constraints :: TypeConstraints
               } deriving (Show)

-- | The type checking monad
type TC = State Env

-- | The empty environment
emptyEnv :: Env
emptyEnv = Env [Map.empty] [] ConsTop

-- | Environment pre-populated with built in gates
initEnv :: Env
initEnv = Env [fmap constType $ Map.fromList stdTypes] [] ConsTop

-- | Modifies the output type constraints
modifyConstraint :: (TypeConstraints -> Maybe TypeConstraints) -> TC () 
modifyConstraint f =  do 
  env <- get
  let c = constraints env
  case f (constraints env) of 
    Nothing -> 
      case c of 
        ConsTop -> return ()
        _ -> return () --logMsg ("The constraints: " ++ (show c) ++ " were modified in an invalid way")
    Just c ->
      put (env { constraints = c })

getConstraint :: TC TypeConstraints
getConstraint = do 
  env <- get 
  return (constraints env)

defaultType :: TypeConstraints -> TC Type
defaultType (ConsCReg i) = return (TCReg i)
defaultType ConsQBit = return TQBit
defaultType (ConsQReg i) = return (TQReg i)
defaultType ConsBool = return TBool
defaultType (ConsUInt mi) = return (TUInt mi)
defaultType (ConsInt mi) = return (TInt mi)
defaultType (ConsAngle mi) = return (TAngle mi)
defaultType (ConsFloat mi) = return (TFloat mi)
defaultType (ConsCmplx mi) = return (TCmplx mi)
defaultType ConsUnit = return TUnit
defaultType (ConsRange c) = do
   t <- defaultType c
   return (TRange t)
defaultType (ConsGate i1 i2) = return (TGate i1 i2)
defaultType (ConsProc cs mc) = do
  ts <- mapM defaultType cs
  mt <- mapM defaultType mc
  return (TProc ts mt)
defaultType ConsTop = --do
--  logMsg "I'm disallowing this! It's just too unconstrained";
  return TUnit

toConstraint :: Type -> TypeConstraints
toConstraint (TCReg x) = ConsCReg x
toConstraint TQBit = ConsQBit
toConstraint (TQReg x) = ConsQReg x
toConstraint TBool = ConsBool
toConstraint (TUInt x) = ConsUInt x
toConstraint (TInt x) = ConsInt x
toConstraint (TAngle x) = ConsAngle x
toConstraint (TFloat x) = ConsFloat x
toConstraint (TCmplx x) = ConsCmplx x
toConstraint TUnit = ConsUnit
toConstraint (TRange x) = ConsRange (toConstraint x)
toConstraint (TGate x y) = ConsGate x y
toConstraint (TProc x y) = ConsProc (fmap toConstraint x) (fmap toConstraint y)

incomingDefaultType :: TC Type 
incomingDefaultType = do 
  env <- get 
  defaultType (constraints env)


-- | Logs an error message
logMsg :: String -> TC ()
logMsg msg = modify (\env -> env { errs = errs env ++ [Err msg] })

-- | Pushes a new scope onto the stack
pushScope :: TC ()
pushScope = modify (\env -> env { scopes = Map.empty:(scopes env) })

-- | Pops the local scope off the stack
popScope :: TC ()
popScope = modify (\env -> env { scopes = tail (scopes env) })

-- | Opens a new procedure scope which contains exactly the global constants
openProcScope :: [(ID, Type)] -> TC [Map ID ElaboratedType]
openProcScope lVars = do
  lScopes <- gets scopes
  let gScope = Map.filter isConstant . head $ reverse lScopes
  modify (\env -> env { scopes = [Map.fromList $ map (fmap pureType) lVars, gScope] })
  return lScopes

-- | Closes a procedure scope, restoring the old scopes
closeProcScope :: [Map ID ElaboratedType] -> TC ()
closeProcScope lScopes = modify (\env -> env { scopes = lScopes })

-- | Looks up an identifier, beginning with the inner-most scope
getBinding :: ID -> TC ElaboratedType
getBinding x = do
  env <- get
  case msum . map (Map.lookup x) $ scopes env of 
    Nothing -> do
        c <- getConstraint
        t <- defaultType c
        let et = pureType t
        assign x et;
        return (pureType t)
    Just x -> return x

-- | Assigns a binding to an identifier. Causes an error if the identifier has a
--   binding in the current scope
assign :: ID -> ElaboratedType -> TC ()
assign var typ = do
  env <- get
  case Map.lookup var (head $ scopes env) of
    Nothing -> put $ env{scopes = (Map.insert var typ . head $ scopes env):(tail $ scopes env)}
    Just _  -> do
      logMsg $ "Error: Declaration of " ++ var ++ " shadows existing declaration"
      return ()

-- | Types of the standard library gates
stdTypes :: [(ID, Type)]
stdTypes = [
  ("gphase", TGate 1 0),
  ("u", TGate 3 1),
  ("p", TGate 1 1),
  ("x", TGate 0 1),
  ("y", TGate 0 1),
  ("z", TGate 0 1),
  ("h", TGate 0 1),
  ("s", TGate 0 1),
  ("sdg", TGate 0 1),
  ("t", TGate 0 1),
  ("tdg", TGate 0 1),
  ("sx", TGate 0 1),
  ("rx", TGate 1 1),
  ("ry", TGate 1 1),
  ("rz", TGate 1 1),
  ("cx", TGate 0 2),
  ("cy", TGate 0 2),
  ("cz", TGate 0 2),
  ("cp", TGate 1 2),
  ("crx", TGate 1 2),
  ("cry", TGate 1 2),
  ("crz", TGate 1 2),
  ("ch", TGate 0 2),
  ("cu", TGate 4 2),
  ("swap", TGate 0 2),
  ("ccx", TGate 0 3),
  ("cswap", TGate 0 3)]
   
{- Indexing behaviour -}

-- | Returns the type of an indexed value of an indexable type
dereference :: Type -> Type
dereference typ = case typ of
  TCReg _  -> TBool
  TQReg _  -> TQBit
  TInt _   -> TBool
  TUInt _  -> TBool
  TAngle _ -> TBool
  _        -> error "Unexpected error: type is not indexable"

{- Casting behaviour -}

-- | Casting rules for openQASM 3 types
castable :: Type -> Type -> Bool
castable from to = case from of
  TBool -> case to of
    TBool    -> True
    TInt _   -> True
    TUInt _  -> True
    TFloat _ -> True
    TCReg _  -> True
    _        -> False
  TInt i -> case to of
    TBool    -> True
    TInt _   -> True
    TUInt _  -> True
    TFloat _ -> True
    TCReg j  -> i == Just j
    _        -> False
  TUInt i -> case to of
    TBool    -> True
    TInt _   -> True
    TUInt _  -> True
    TFloat _ -> True
    TCReg j  -> i == Just j
    _        -> False
  TFloat _ -> case to of
    TBool    -> True
    TInt _   -> True
    TUInt _  -> True
    TFloat _ -> True
    TAngle _ -> True
    _        -> False
  TAngle i -> case to of
    TBool    -> True
    TAngle _ -> True
    TCReg j  -> i == Just j
    _        -> False
  TCReg i -> case to of
    TBool    -> True
    TInt j   -> Just i == j
    TUInt j  -> case j of
      Just j  -> i == j
      Nothing -> True
    TAngle j -> Just i == j
    TCReg j  -> i == j
    _         -> False
  TQBit -> case to of
    TQBit -> True
    _     -> False
  TQReg _ -> case to of
    TQReg _ -> True
    _       -> False
  TRange t -> case to of
    TRange t' -> castable t t'
  _ -> False

-- | Unification of types in expressions
--
--   Based on the greater than relation in the openQASM 3 and integer promotion rules (C99)
unify :: Type -> Type -> Maybe Type
unify a b | a == b = Just a
          | otherwise = case a of
              TBool -> case b of
                TBool    -> Just $ TBool
                TInt j   -> Just $ TInt j
                TUInt j  -> Just $ TUInt j
                TFloat j -> Just $ TFloat j
                TCmplx j -> Just $ TCmplx j
                _        -> Nothing
              TInt i -> case b of
                TBool    -> Just $ TInt i
                TInt j   -> Just $ TInt (unifyWidth i j)
                TUInt j  -> Just $ TInt (unifyWidth i (fmap (+1) j))
                TFloat j -> Just $ TFloat j
                TCmplx j -> Just $ TCmplx j
                _        -> Nothing
              TUInt i -> case b of
                TBool    -> Just $ TUInt i
                TInt j   -> Just $ TInt (unifyWidth (fmap (+1) i) j)
                TUInt j  -> Just $ TUInt (unifyWidth i j)
                TFloat j -> Just $ TFloat j
                TCmplx j -> Just $ TCmplx j
                _        -> Nothing
              TFloat i -> case b of
                TBool    -> Just $ TFloat i
                TInt j   -> Just $ TFloat i
                TUInt j  -> Just $ TFloat i
                TFloat j -> Just $ TFloat (unifyWidth i j)
                TCmplx j -> Just $ TCmplx j
                _        -> Nothing
              TCmplx i -> case b of
                TBool    -> Just $ TCmplx i
                TInt j   -> Just $ TCmplx i
                TUInt j  -> Just $ TCmplx i
                TFloat j -> Just $ TCmplx i
                TCmplx j -> Just $ TCmplx (unifyWidth i j)
                _        -> Nothing
              TAngle i -> case b of
                TAngle j -> Just $ TAngle (unifyWidth i j)
                _        -> Nothing
              TCReg i -> case b of
                TCReg j -> Just $ TCReg (max i j)
                _       -> Nothing

-- | Unifies widths of sized types
unifyWidth :: Maybe Integer -> Maybe Integer -> Maybe Integer
unifyWidth Nothing  _        = Nothing
unifyWidth _        Nothing  = Nothing
unifyWidth (Just i) (Just j) = Just (max i j)

-- | Unary operator type lookup
tcUOp :: UOp -> Type -> Maybe Type
tcUOp uop typ = case uop of
  SinOp      | castable typ (TAngle Nothing) -> Just (TAngle Nothing)
  SinOp      | castable typ (TFloat Nothing) -> Just (TFloat Nothing)
  CosOp      | castable typ (TAngle Nothing) -> Just (TAngle Nothing)
  CosOp      | castable typ (TFloat Nothing) -> Just (TFloat Nothing)
  TanOp      | castable typ (TAngle Nothing) -> Just (TAngle Nothing)
  TanOp      | castable typ (TFloat Nothing) -> Just (TFloat Nothing)
  ArcsinOp   | castable typ (TFloat Nothing) -> Just (TFloat Nothing)
  ArccosOp   | castable typ (TFloat Nothing) -> Just (TFloat Nothing)
  ArctanOp   | castable typ (TFloat Nothing) -> Just (TFloat Nothing)
  CeilOp     | castable typ (TFloat Nothing) -> Just (TFloat Nothing)
  FloorOp    | castable typ (TFloat Nothing) -> Just (TFloat Nothing)
  ExpOp      | castable typ (TFloat Nothing) -> Just (TFloat Nothing)
  ExpOp      | castable typ (TCmplx Nothing) -> Just (TCmplx Nothing)
  ExpOp      | castable typ (TBool)          -> Just (TFloat Nothing)
  LnOp       | castable typ (TFloat Nothing) -> Just (TFloat Nothing)
  SqrtOp     | castable typ (TFloat Nothing) -> Just (TFloat Nothing)
  SqrtOp     | castable typ (TCmplx Nothing) -> Just (TCmplx Nothing)
  RealOp     | castable typ (TCmplx Nothing) -> Just (TFloat Nothing)
  ImOp       | castable typ (TCmplx Nothing) -> Just (TFloat Nothing)
  NegOp      | isBitvec typ                 -> Just typ
  UMinusOp   | isNumeric typ                -> Just typ
  PopcountOp | castable typ (TUInt Nothing) -> Just (TUInt Nothing)
  _                                             -> Nothing

-- | Binary operator type lookup
tcBOp :: Type -> BinOp -> Type -> Maybe Type
tcBOp typ bop typ' = case bop of
  AndOp    | isBitvec typ && isBitvec typ' -> typ''
  OrOp     | isBitvec typ && isBitvec typ' -> typ''
  XorOp    | isBitvec typ && isBitvec typ' -> typ''
  LShiftOp | isBitvec typ && castable typ' (TUInt Nothing) -> Just typ
  RShiftOp | isBitvec typ && castable typ' (TUInt Nothing) -> Just typ
  LRotOp   | isBitvec typ && castable typ' (TUInt Nothing) -> Just typ
  RRotOp   | isBitvec typ && castable typ' (TUInt Nothing) -> Just typ
  EqOp     | isJust typ'' && isComparable (fromJust typ'') -> Just TBool
  NEqOp    | isJust typ'' && isComparable (fromJust typ'') -> Just TBool
  LTOp     | isJust typ'' && isComparable (fromJust typ'') -> Just TBool
  LEqOp    | isJust typ'' && isComparable (fromJust typ'') -> Just TBool
  GTOp     | isJust typ'' && isComparable (fromJust typ'') -> Just TBool
  GEqOp    | isJust typ'' && isComparable (fromJust typ'') -> Just TBool
  PlusOp   | isNumeric typ && isNumeric typ' -> typ''
  PlusOp   | isQuantum typ && isQuantum typ' -> typ''
  MinusOp  | isNumeric typ && isNumeric typ' -> typ''
  TimesOp  | isNumeric typ && isQuantum typ' -> Just typ'
  TimesOp  | isNumeric typ && isNumeric typ' -> typ''
  TimesOp  | isBitvec typ && isBitvec typ'   -> typ''
  DivOp    | isNumeric typ && isNumeric typ' -> typ''
  ModOp    | isNumeric typ && isNumeric typ' -> Just typ
  PowOp    | isNumeric typ && isNumeric typ' -> typ''
  ConcatOp | isIndexable typ && isIndexable typ' -> typ''
  _ -> Nothing
  where typ'' = unify typ typ'

{- Semantic analysis & type checking -}

-- | Program type checking
tcProg :: Prog Location -> TC (Prog ElaboratedType)
tcProg (Prog ver xs) = liftM (Prog ver) $ mapM tcStmt xs

-- | Declaration type checking
tcDecl :: Decl Location -> TC (Decl ElaboratedType)
tcDecl decl = case decl of
  DVar var typ val isConstant -> do
    typ <- resolveType typ
    val <- mapM (flip tcExprAs typ) val
    intVal <- case (isConstant, typ, val) of
      (True,TInt _,Just expr)  -> evalUInt expr >>= return . Just
      (True,TUInt _,Just expr) -> evalUInt expr >>= return . Just
      _                        -> return Nothing
    let etype = EType typ isConstant intVal
    assign var etype
    return $ DVar var (asTypeExpr' typ) val isConstant

  DDef var params ret body -> do
    let (ids,types) = unzip params
    paramTypes <- mapM resolveType types
    let params = zip ids paramTypes
    ret <- mapM resolveType ret
    let fTyp = TProc paramTypes ret
    scopes <- openProcScope $ (var,fTyp):params
    body <- tcStmt body
    closeProcScope scopes
    assign var (constType fTyp)
    return  $ DDef var (map (fmap asTypeExpr') params) (fmap asTypeExpr' ret) body

  DGate var cparams qparams body -> do
    let fTyp = TGate (length cparams) (length qparams)
    scopes <- openProcScope $ [(var,fTyp)] ++ (zip cparams $ repeat (TAngle Nothing)) ++ (zip qparams $ repeat TQBit)
    body <- tcStmt body
    closeProcScope scopes
    assign var (constType fTyp)
    return  $ DGate var cparams qparams body

  DExtern var params ret -> do
    params <- mapM resolveType params
    ret    <- mapM resolveType ret
    assign var (constType $ TProc params ret)
    return $ DExtern var (map asTypeExpr' params) (fmap asTypeExpr' ret)

  DAlias var exprs -> do
    let isQReg typ = case typ of
          TQReg _ -> True
          _       -> False
    exprs <- mapM tcExpr exprs
    case map typeof exprs of
      [TQBit] -> assign var (pureType TQBit)
      xs | all isQReg xs -> assign var (pureType $ TQReg (foldr (\(TQReg i) -> (+i)) 0 xs))
      _ -> logMsg "Type error: aliased values should be qbit or qreg type"
    return $ DAlias var exprs
    

-- | Statement type checking. Expands some statements
--   to lists of statements
tcStmt :: Stmt Location -> TC (Stmt ElaboratedType)
tcStmt stmt = case stmt of
  SSkip loc -> return $ SSkip unitTy

  SDeclare loc decl -> liftM (SDeclare unitTy) $ tcDecl decl

  SBarrier loc xs -> liftM (SBarrier unitTy) $ mapM tcAccessPath xs

  SBlock loc xs -> do
    pushScope
    stmts <- mapM tcStmt xs
    popScope
    return $ SBlock unitTy stmts

  SExpr loc expr -> liftM (SExpr unitTy) $ tcExpr expr

  SGateCall loc mods id cargs qargs -> getBinding id >>= \(EType (TGate nC nQ) _ _) -> do
      mods <- mapM tcModifier mods
      cargs <- mapM (flip tcExprAs (TFloat Nothing)) cargs
      qargs <- broadcast =<< mapM tcAccessPath qargs
      case qargs of
        []      -> do
          logMsg $ "Type error at (" ++ show loc ++ "): Gate arguments not broadcastable"
          return $ SGateCall unitTy mods id cargs []
        [qargs] -> return $ SGateCall unitTy mods id cargs qargs
        _       -> return $ SBlock unitTy $ map (SGateCall unitTy mods id cargs) qargs

  SAssign loc ap expr -> do
    ap <- tcAccessPath ap
    let (EType ty isConstant _) = getAnnotation ap
    when isConstant $
      logMsg $ "Error at (" ++ show loc ++ "): Modifying constant lvalue " ++ show ap
    expr <- tcExprAs expr (typeof ap)
    return $ SAssign unitTy ap expr

  SFor loc (var, typ) expr stmt -> do
    typ <- resolveType typ
    expr <- tcExprAs expr (TRange typ)
    pushScope
    assign var (pureType typ)
    stmt <- tcStmt stmt
    popScope
    return $ SFor unitTy (var, asTypeExpr' typ) expr stmt

  SBreak loc    -> return $ SBreak unitTy
  SContinue loc -> return $ SContinue unitTy
  SEnd loc      -> return $ SEnd unitTy

  SIf loc expr stmt stmt' -> do
    expr <- tcExprAs expr TBool
    stmt <- tcStmt stmt
    stmt' <- tcStmt stmt'
    return $ SIf unitTy expr stmt stmt'

  SReset loc expr -> do
    expr <- tcExpr expr
    case typeof expr of
      TQBit   -> return $ SReset unitTy expr
      TQReg _ -> return $ SReset unitTy expr
      _       -> do
        logMsg $ "Type error at (" ++ show loc ++ "): reset of non-qubit or qreg argument"
        return $ SReset unitTy expr

  SReturn loc mexpr -> do
    mexpr <- mapM tcExpr mexpr
    return $ SReturn unitTy mexpr

  SWhile loc expr stmt -> do
    expr <- tcExprAs expr TBool
    stmt <- tcStmt stmt
    return $ SWhile unitTy expr stmt

  SAnnotated loc annots stmt -> do
    annots <- mapM (tcAnnotation stmt) annots
    stmt <- tcStmt stmt
    return $ SAnnotated unitTy annots stmt

  SPragma loc str -> return $ SPragma unitTy str

  where unitTy = pureType TUnit
    
-- | Broadcasting gate arguments
broadcast :: [AccessPath ElaboratedType] -> TC [[AccessPath ElaboratedType]]
broadcast xs = case foldM go (-1) xs of
  Nothing   -> return [[]]
  Just (-1) -> return [xs]
  Just i    -> return [map (deref j) xs | j <- [0..i-1]]
  where
    go i ap = case (i, getAnnotation ap) of
      (i, EType TQBit _ _)      -> Just i
      (-1, EType (TQReg j) _ _) -> Just j
      (i, EType (TQReg j) _ _)  -> if i == j then Just i else Nothing

    deref i ap = case ap of
      AVar (EType (TQReg _) c v) var ->
        AIndex (EType TQBit c v) var (EInt (pureType $ TUInt Nothing) i)
      _                            -> ap
      
tcEq :: (AccessPath Location,Expr Location) -> TC (AccessPath ElaboratedType,Expr ElaboratedType)
tcEq (ap,e) = do 
  ap <- tcAccessPath ap
  let et = typeof ap
  modifyConstraint (\_ -> Just (toConstraint et));
  e <- tcExpr e
  return (ap,e)

tcAnnotation :: Stmt Location -> Annotation Location -> TC (Annotation ElaboratedType)
tcAnnotation _ (Other ss) = return (Other ss)
tcAnnotation _ (Assert eqs) = do
  eqs <- mapM tcEq eqs
  return (Assert eqs)
tcAnnotation _ (Fn (e1,e2)) = do 
  e1 <- tcExpr e1
  e2 <- tcExpr e2
  return (Fn (e1, e2))
tcAnnotation stmt (Triple pre post refs) = case stmt of
  SDeclare _ decl -> 
    let params = case decl of
          DDef  {dparams = p} -> p
          DGate {gparams = p, gqargs = args} -> zip p (repeat $ TAngle Nothing) ++ zip args (repeat TQBit)
    in do
    let (ids, typeExprs) = unzip params
    types <- mapM resolveType typeExprs
    scope <- openProcScope (zip ids types)
    pre <- mapM tcEq pre
    post <- mapM tcEq post
    refs <- mapM tcExpr refs
    closeProcScope scope
    return (Triple pre post refs)

-- | Expression type checking
tcExpr :: Expr Location -> TC (Expr ElaboratedType)
tcExpr expr0 = case expr0 of
  EVar loc var -> do
    typ <- getBinding var
    return $ EVar typ var

  EIndex loc expr idx -> do
    expr <- tcExpr expr
    idx <- tcExpr idx
    let annot = getAnnotation expr
    case (isIndexable (ty annot), typeof idx) of
      (False, _) -> do
        logMsg $ "Type error at (" ++ show loc ++ "): expected indexable type"
        return $ EIndex annot expr idx
      (True, TRange idxTyp) | castable idxTyp (TUInt Nothing) ->
        return $ EIndex annot expr idx
      (True, idxTyp) | castable idxTyp (TUInt Nothing) ->
        return $ EIndex (annot { ty = dereference (ty annot) }) expr idx
      _ -> do
        logMsg $ "Type error at (" ++ show loc ++ "): invalid index type"
        return $ EIndex annot expr idx

  ECall loc var args -> do
    modifyConstraint 
      (\c -> 
        case c of 
          ConsTop -> Just ConsTop
          _ -> Just (ConsProc (repeat ConsTop) (Just c)))
    bind <- getBinding var
    case bind of
      (EType (TProc params ret) _ _) -> do
        modifyConstraint (\_ -> Just ConsTop);
        args <- mapM (uncurry tcExprAs) (zip args params)
        return $ ECall (pureType $ fromMaybe TUnit ret) var args 
      _ -> do
        logMsg $ "Type error at (" ++ show loc ++"): procedure type expected"
        args <- mapM tcExpr args
        return $ ECall (pureType TUnit) var args

  EMeasure loc expr -> do
    modifyConstraint 
      (\c -> 
        case c of 
          ConsBool -> Just ConsQBit
          ConsCReg i -> Just (ConsQReg i)
          _ -> Nothing)
    expr <- tcExpr expr
    case typeof expr of
      TQBit   -> return $ EMeasure (pureType TBool) expr
      TQReg i -> return $ EMeasure (pureType $ TCReg i) expr
      _       -> do
        logMsg $ "Type error at (" ++ show loc ++ "): measure of non-qubit or qreg argument"
        return $ EMeasure (pureType TBool) expr

  EInt loc i   -> return $ EInt (constInt (TInt Nothing) i) i
  EBits loc xs -> return $ EBits (constType (TCReg $ toInteger $ length xs)) xs
  EFloat loc r -> return $ EFloat (constType (TFloat Nothing)) r
  ECmplx loc c -> return $ ECmplx (constType (TCmplx Nothing)) c

  ESlice loc init step end -> do
    init <- tcExprAs init (TInt Nothing)
    step <- mapM (flip tcExprAs $ TInt Nothing) step
    end  <- tcExprAs end (TInt Nothing)
    return $ ESlice (pureType $ TRange (TUInt Nothing)) init step end
    
  ESet loc exprs -> do
    exprs <- mapM (flip tcExprAs $ TUInt Nothing) exprs
    return $ ESet (pureType $ TRange (TUInt Nothing)) exprs

  EPi loc -> return $ EPi (constType (TFloat Nothing))
  EIm loc -> return $ EIm (constType (TCmplx Nothing))
  EBool loc b -> return $ EBool (constType TBool) b

  EUOp loc uop expr -> do
    expr <- tcExpr expr
    let annot = getAnnotation expr
    case tcUOp uop (ty annot) of
      Nothing -> do
        logMsg $ "Type error at (" ++ show loc ++ ") in " ++ prettyPrintExpr expr0
        return $ EUOp annot uop expr
      Just rTyp -> return $ EUOp (annot { ty = rTyp }) uop expr

  EBOp loc expr bop expr' -> do
    expr <- tcExpr expr
    expr' <- tcExpr expr'
    case tcBOp (typeof expr) bop (typeof expr') of
      Nothing -> do
        logMsg $ show expr ++ ": " ++ show (typeof expr)
        logMsg $ show expr' ++ ": " ++ show (typeof expr')
        logMsg $ "Type error at (" ++ show loc ++ ") in " ++ prettyPrintExpr expr0
        return $ EBOp (getAnnotation expr) expr bop expr'
      Just rTyp ->
        let isConstTy = isConstant . getAnnotation in
          return $ EBOp (EType rTyp (isConstTy expr && isConstTy expr') Nothing) expr bop expr'

  EStmt loc stmt -> do
    stmt <- tcStmt stmt
    return $ EStmt (pureType TUnit) stmt

  ECast loc typexpr expr -> do
    typ <- resolveType typexpr
    modifyConstraint (\_ -> Just (toConstraint typ));
    expr <- tcExpr expr
    when (not $ castable (typeof expr) typ) $
      logMsg $ "Type error at (" ++ show loc  ++ "): invalid cast"
    return $ ECast ((getAnnotation expr){ ty = typ }) (asTypeExpr' typ) expr
        
  EVarDec loc id typexpr -> do
    typ <- resolveType typexpr
    let etyp = pureType typ
    assign id etyp
    return $ EVarDec etyp id (asTypeExpr' typ)
  
  Ket loc expr -> do
    modifyConstraint 
      (\c -> case c of
        ConsQBit -> Just ConsBool
        ConsQReg i -> Just $ ConsCReg i
        _          -> Just c)
    expr <- tcExpr expr
    case typeof expr of
      TBool          -> return $ Ket (pureType TQBit) expr
      TCReg n        -> return $ Ket (pureType (TQReg n)) expr
      TUInt (Just n) -> return $ Ket (pureType (TQReg n)) expr
      TInt _  -> case value . getAnnotation $ expr of
        Just 0 -> return $ Ket (pureType TQBit) (EBool (pureType TBool) False)
        Just 1 -> return $ Ket (pureType TQBit) (EBool (pureType TBool) True)
      _       -> error $ show expr

  Fun _ _ _ -> error "TODO"

  Sum loc binds expr -> do
    c <- getConstraint
    let (ids, types) = unzip binds
    bindTypes <- mapM (maybe (return TBool) resolveType) types
    let binds = zip ids bindTypes
    pushScope
    mapM (\(id, ty) -> assign id (pureType ty)) binds
    expr <- tcExpr expr
    popScope
    let binds = zip ids (fmap (Just . asTypeExpr') bindTypes)
    return $ Sum (getAnnotation expr) binds expr

  Tensor loc expr1 expr2 -> do
    expr1 <- tcExpr expr1
    expr2 <- tcExpr expr2
    let ty = case (typeof expr1, typeof expr2) of
          (TQReg n , TQReg m) -> TQReg (n+m)
          (TQBit   , TQReg m) -> TQReg (m+1)
          (TQReg n , TQBit  ) -> TQReg (n+1)
          (TQBit   , TQBit  ) -> TQReg 2
          (TFloat _, TQBit  ) -> TQBit
          (TFloat _, TQReg m) -> TQReg m
          (TQBit   , TFloat _) -> TQBit
          (TQReg m , TFloat _) -> TQReg m
          (TBool   , t      ) -> t
          (t, s) -> error $ show t ++ " -- " ++ show expr1 ++ " otimes " ++ show expr2
    return $ Tensor (pureType ty) expr1 expr2

    -- let (ids,types) = unzip params
    -- paramTypes <- mapM resolveType types
    -- let params = zip ids paramTypes
    -- ret <- mapM resolveType ret
    -- let fTyp = TProc paramTypes ret
    -- scopes <- openProcScope $ (var,fTyp):params
    -- body <- tcStmt body
    -- closeProcScope scopes
    -- assign var (constType fTyp)
  _ -> error $ show expr0


-- | Evaluates a suitably typed expression as a UInt
evalUInt :: Expr ElaboratedType -> TC Integer
evalUInt expr = case expr of
  EVar _ var -> getBinding var >>= return . fromJust . value
  EInt _ i -> return i
  EBits _ xs -> return $ foldr (+) 0 . map (\(b,i) -> if b then shift 1 i else 0) $ zip xs [0..]
  EUOp _ uop expr -> liftM (evalUOp uop) $ evalUInt expr
  EBOp _ expr bop expr' ->
    pure (\a b -> evalBOp a bop b) <*> (evalUInt expr) <*> (evalUInt expr')
  ECast _ _ expr -> evalUInt expr
  _ -> error "Unimplemented"
  where evalUOp :: UOp -> Integer -> Integer
        evalUOp uop i = case uop of
          UMinusOp -> (-i)
          NegOp -> complement i
          PopcountOp -> toInteger (popCount ((fromIntegral i) :: Int))
        evalBOp :: Integer -> BinOp -> Integer -> Integer
        evalBOp i bop j = case bop of
          AndOp -> i .&. j
          OrOp -> i .|. j
          XorOp -> i `xor` j
          LShiftOp -> i `shiftL` (fromIntegral j)
          RShiftOp -> i `shiftR` (fromIntegral j)
          LRotOp -> i `rotateL` (fromIntegral j)
          RRotOp -> i `rotateR` (fromIntegral j)
          PlusOp -> i + j
          MinusOp -> i - j
          TimesOp -> i * j
          DivOp -> i `div` j
          ModOp -> i `mod` j
          PowOp -> i^j
          
  
-- | Type checks an expression as a particular type, inserting
--   a cast as needed
tcExprAs :: Expr Location -> Type -> TC (Expr ElaboratedType)
tcExprAs expr typ = do
  expr <- tcExpr expr
  let exprType = getAnnotation expr
  if typ == ty (exprType) then
    return expr
  else case castable (ty exprType) typ of
    False -> do
      logMsg $ "Type error at (" ++ show (getAnnotation expr) ++ "): " ++
               "Expected type " ++ show typ ++ ", got " ++ show (ty exprType)
      return $ expr
    True -> return $ ECast (exprType { ty = typ }) (asTypeExpr' typ) expr

-- | Expression type checking
tcModifier :: Modifier Location -> TC (Modifier ElaboratedType)
tcModifier mod = case mod of
  MCtrl loc neg mexpr -> do
    mexpr <- mapM (flip tcExprAs (TUInt Nothing)) mexpr
    return $ MCtrl (pureType TUnit) neg mexpr
  MInv loc -> return $ MInv (pureType TUnit)
  MPow loc expr -> do
    expr <- tcExprAs expr (TUInt Nothing)
    return $ MPow (pureType TUnit) expr

-- | Access Path type checking
tcAccessPath :: AccessPath Location -> TC (AccessPath ElaboratedType)
tcAccessPath ap = case ap of
  AVar loc var -> do
    typ <- getBinding var
    case typ of
      typ -> return $ AVar typ var
  AIndex loc var expr -> do
    typ <- getBinding var
    expr <- tcExpr expr
    case (typ, isIndexable (ty typ), typeof expr) of
      (typ, False, _) -> do
        logMsg $ "Type error at (" ++ show loc ++ "): variable " ++ var ++ " cannot be indexed"
        return $ AIndex typ var expr
      (typ, _, TRange idxTyp) | castable idxTyp (TUInt Nothing) ->
        return $ AIndex typ var expr
      (typ, _, idxTyp) | castable idxTyp (TUInt Nothing) ->
        return $ AIndex (typ { ty = dereference (ty typ) }) var expr
      _ -> do
        logMsg $ "Type error at (" ++ show loc ++ "): invalid index type"
        return $ AIndex (pureType TUnit) var expr
  AList loc [] -> return $ AList (pureType (TFloat Nothing)) []
  AList loc paths -> do
    paths <- mapM tcAccessPath paths
    let p = head paths
    let listtype = if isQuantum (typeof p) then
          foldl addType (TQReg 0) paths
        else
          foldl addType (TCReg 0) paths
    return $ AList (pureType listtype) paths
  where
    addType t a = case (isQuantum t, isQuantum (typeof a)) of
      (True , True ) -> TQReg (length t + length (typeof a))
      (False, False) -> TCReg (length t + length (typeof a))
    length t = case t of
      TQBit          -> 1
      TQReg n        -> n
      TBool          -> 1
      TCReg n        -> n
      TUInt (Just n) -> n

-- | Resolves a type
resolveType :: TypeExpr Location -> TC Type
resolveType typ = case typ of
  TCReg expr       -> tcSize expr >>= return . TCReg
  TQBit            -> return TQBit
  TQReg expr       -> tcSize expr >>= return . TQReg
  TBool            -> return TBool
  TUInt expr       -> mapM tcSize expr >>= return . TUInt
  TInt expr        -> mapM tcSize expr >>= return . TInt
  TAngle expr      -> mapM tcSize expr >>= return . TAngle
  TFloat expr      -> mapM tcSize expr >>= return . TFloat
  TCmplx expr      -> mapM tcSize expr >>= return . TCmplx
  TUnit            -> return TUnit
  TRange ty        -> resolveType ty >>= return . TRange
  TGate nc nq      -> return $ TGate nc nq
  TProc at rt      -> pure TProc <*> mapM resolveType at <*> mapM resolveType rt

  where

    tcSize = tcExpr >=> resolveExpr

    resolveExpr expr = case getAnnotation expr of
      EType _ False _ -> do
        logMsg $ "Error: type parameterized by non-constant expression"
        return $ 0
      EType typ True _ | castable typ (TUInt Nothing) -> evalUInt expr

{- Top-level type checking -}

-- | Type checks a program and converts the result into an alternative
tcQasm :: Prog Location -> Either [ErrMsg] (Prog ElaboratedType)
tcQasm prog = case runState (tcProg prog) initEnv of
  (prog, Env _ [] _) -> Right prog
  (_, Env _ xs _)    -> Left xs

-- | Prints out the list of error messages
printErrors :: [ErrMsg] -> IO ()
printErrors = mapM_ (\a -> print a >> putStrLn "")
