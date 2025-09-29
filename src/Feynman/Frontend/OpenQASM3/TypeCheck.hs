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
import Data.Maybe (fromJust)

import Feynman.Core (ID)
import qualified Feynman.Frontend.OpenQASM3.Syntax as S
import Feynman.Frontend.OpenQASM3.Core

{- Types -}

-- | Type elaborate with compile-time constant declarations
data ElaboratedType = EType { ty :: Type,
                              const :: Bool
                            } deriving (Show)

-- | Insert a type into an elaborated type
pureType :: Type -> ElaboratedType
pureType ty = EType ty False

-- | Insert a constant type into an elaborated type
constType :: Type -> ElaboratedType
constType ty = EType ty True

-- | Gets the base type of an AST node annotated with an elaborated type
typeof :: Annotated f => f ElaboratedType -> Type
typeof = ty . getAnnotation

-- | Instance for asTypeExpr specialized to type checking
asTypeExpr' :: Type -> TypeExpr ElaboratedType
asTypeExpr' = asTypeExpr (pureType $ TUInt Nothing)

-- | Type checking environment, consisting of bindings to
--   elaborate types and a list of error messages
data Env = Env { constants :: Map ID ElaboratedType,
                 scopes :: [Map ID ElaboratedType],
                 errs  :: [ErrMsg]
               } deriving (Show)

-- | The type checking monad
type TC = State Env

-- | The empty environment
emptyEnv :: Env
emptyEnv = Env Map.empty [Map.empty] []

-- | Logs an error message
logMsg :: String -> TC ()
logMsg msg = modify (\env -> env { errs = errs env ++ [Err msg] })

-- | Pushes a new scope onto the stack
pushScope :: TC ()
pushScope = modify (\env -> env { scopes = Map.empty:(scopes env) })

-- | Pops the local scope off the stack
popScope :: TC ()
popScope = modify (\env -> env { scopes = Map.empty:(scopes env) })

-- | Opens a new procedure scope which contains exactly the global constants
openProcScope :: [(ID, Type)] -> TC [Map ID ElaboratedType]
openProcScope lVars = do
  lScopes <- gets scopes
  modify (\env -> env { scopes = [Map.fromList $ map (fmap pureType) lVars] })
  return lScopes

-- | Closes a procedure scope, restoring the old scopes
closeProcScope :: [Map ID ElaboratedType] -> TC ()
closeProcScope lScopes = modify (\env -> env { scopes = lScopes })

-- | Looks up an identifier, beginning with the inner-most scope
getBinding :: ID -> TC (Maybe ElaboratedType)
getBinding x = do
  env <- get
  return . msum . map (Map.lookup x) $ scopes env ++ [constants env]

-- | Assigns a binding to an identifier. Causes an error if the identifier has a
--   binding in the current scope
assign :: ID -> ElaboratedType -> TC ()
assign var typ = do
  env <- get
  case Map.lookup var (head $ scopes env) of
    Nothing -> put $ env{scopes = (Map.insert var typ . head $ scopes env):(tail $ scopes env)}
    Just _  -> do
      logMsg $ "Error: Declaration of " ++ var ++ " shadows existing definition"
      return ()

{- Indexing behaviour -}

-- | Checks whether a type can be indexed
isIndexable :: Type -> Bool
isIndexable typ = case typ of
  TCReg _  -> True
  TQReg _  -> True
  TInt _   -> True
  TUInt _  -> True
  TAngle _ -> True
  _        -> False

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
    TUInt j  -> Just i == j
    TAngle j -> Just i == j
    TCReg j  -> i == j
    _         -> False
  TQBit -> case to of
    TQBit -> True
    _     -> False
  TQReg _ -> case to of
    TQReg _ -> True
    _       -> False
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
unifyWidth :: Maybe Int -> Maybe Int -> Maybe Int
unifyWidth Nothing  _        = Nothing
unifyWidth _        Nothing  = Nothing
unifyWidth (Just i) (Just j) = Just (max i j)

{- Semantic analysis & type checking -}

-- | Program type checking
tcProg :: Prog Location -> TC (Prog ElaboratedType)
tcProg (Prog ver xs) = liftM (Prog ver) $ mapM tcStmt xs

-- | Declaration type checking
tcDecl :: Decl Location -> TC (Decl ElaboratedType)
tcDecl decl = case decl of
  DVar var typ val isConst -> do
    typ <- resolveType typ
    val <- mapM (flip tcExprAs typ) val
    assign var (EType typ isConst)
    return $ DVar var (asTypeExpr' typ) val isConst

  DDef var params ret body -> do
    let (ids,types) = unzip params
    paramTypes <- mapM resolveType types
    let params = zip ids paramTypes
    ret <- mapM resolveType ret
    let fTyp = TProc paramTypes ret
    scopes <- openProcScope $ (var,fTyp):params
    body <- tcStmt body
    closeProcScope scopes
    assign var (EType fTyp True)
    return  $ DDef var (map (fmap asTypeExpr') params) (fmap asTypeExpr' ret) body

  DGate var cparams qparams body -> do
    let (ids,types) = unzip cparams
    paramTypes <- mapM resolveType types
    let cparams = zip ids paramTypes
    let fTyp = TGate (length cparams) (length qparams)
    scopes <- openProcScope $ [(var,fTyp)] ++ cparams ++ (zip qparams $ repeat TQBit)
    body <- tcStmt body
    closeProcScope scopes
    assign var (EType fTyp True)
    return  $ DGate var (map (fmap asTypeExpr') cparams) qparams body

  DExtern var params ret -> do
    params <- mapM resolveType params
    ret    <- mapM resolveType ret
    assign var (EType (TProc params ret) True)
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

  SGateCall loc mods id cargs qargs -> getBinding id >>= \record -> case record of

    Nothing -> do
      logMsg $ "Error at (" ++ show loc ++ "): undeclared identifier " ++ id
      return $ SGateCall unitTy [] id [] []

    Just (EType (TGate nC nQ) _) -> do
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
    let (EType ty const) = getAnnotation ap
    when const $
      logMsg $ "Error at (" ++ show loc ++ "): Modifying constant lvalue " ++ show ap
    expr <- tcExprAs expr (typeof ap)
    return $ SAssign unitTy ap expr

  SFor loc (var, typ) expr stmt -> do
    typ <- resolveType typ
    expr <- tcExprAs expr (TRange typ)
    pushScope
    assign var (EType typ False)
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
    stmt <- tcStmt stmt
    return $ SAnnotated unitTy annots stmt

  SPragma loc str -> return $ SPragma unitTy str

  where unitTy = EType TUnit False
    
-- | Broadcasting gate arguments
broadcast :: [AccessPath ElaboratedType] -> TC [[AccessPath ElaboratedType]]
broadcast _ = error "Unimplemented"

-- | Expression type checking
tcExpr :: Expr Location -> TC (Expr ElaboratedType)
tcExpr _ = error "Unimplemented"

-- | Evaluates a suitably typed expression as a UInt
evalUInt :: Expr ElaboratedType -> TC Int
evalUInt _ = error "Unimplemented"

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
      Nothing -> do
        logMsg $ "Error at (" ++ show loc ++ "): undeclared identifier " ++ var
        return $ AVar (pureType TUnit) var
      Just typ -> return $ AVar typ var
  AIndex loc var expr -> do
    typ <- getBinding var
    expr <- tcExpr expr
    case (typ, isIndexable (ty $ fromJust typ), typeof expr) of
      (Nothing, _, _) -> do
        logMsg $ "Error at (" ++ show loc ++ "): undeclared identifier " ++ var
        return $ AVar (pureType TUnit) var
      (Just typ, False, _) -> do
        logMsg $ "Type error at (" ++ show loc ++ "): variable " ++ var ++ " cannot be indexed"
        return $ AIndex typ var expr
      (Just typ, _, TRange idxTyp) | castable idxTyp (TUInt Nothing) ->
        return $ AIndex typ var expr
      (Just typ, _, idxTyp) | castable idxTyp (TUInt Nothing) ->
        return $ AIndex (typ { ty = dereference (ty typ) }) var expr
      _ -> do
        logMsg $ "Type error at (" ++ show loc ++ "): invalid index type"
        return $ AIndex (pureType TUnit) var expr

-- | Resolves a type
resolveType :: TypeExpr Location -> TC Type
resolveType typ = case typ of
  TCReg expr  -> tcSize expr >>= return . TCReg
  TQBit       -> return TQBit
  TQReg expr  -> tcSize expr >>= return . TQReg
  TBool       -> return TBool
  TUInt expr  -> mapM tcSize expr >>= return . TUInt
  TInt expr   -> mapM tcSize expr >>= return . TInt
  TAngle expr -> mapM tcSize expr >>= return . TAngle
  TFloat expr -> mapM tcSize expr >>= return . TFloat
  TCmplx expr -> mapM tcSize expr >>= return . TCmplx
  TUnit       -> return TUnit
  TRange ty   -> resolveType ty >>= return . TRange
  TGate nc nq -> return $ TGate nc nq
  TProc at rt -> pure TProc <*> mapM resolveType at <*> mapM resolveType rt

  where

    tcSize = tcExpr >=> resolveExpr

    resolveExpr expr = case getAnnotation expr of
      EType _ False -> do
        logMsg $ "Error: type parameterized by non-constant expression"
        return $ 0
      EType typ True | castable typ (TUInt Nothing) -> evalUInt expr
