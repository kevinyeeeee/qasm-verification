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

import Feynman.Core (ID)
import qualified Feynman.Frontend.OpenQASM3.Syntax as S
import Feynman.Frontend.OpenQASM3.Core

{- Types -}

-- | Type elaborate with compile-time constant declarations
data ElaboratedType = EType { ty :: ResolvedType,
                              const :: Bool
                            } deriving (Show)

-- | Insert a type into an elaborated type
pureType :: ResolvedType -> ElaboratedType
pureType ty = EType ty False

-- | Insert a constant type into an elaborated type
constType :: ResolvedType -> ElaboratedType
constType ty = EType ty True

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

-- | Looks up an identifier, beginning with the inner-most scope
getBinding :: ID -> TC (Maybe ElaboratedType)
getBinding x = do
  env <- get
  return . msum . map (Map.lookup x) $ scopes env ++ [constants env]

{- Casting behaviour -}

-- | Casting rules for openQASM 3 types
castable :: ResolvedType -> ResolvedType -> Bool
castable from to = case from of
  TBool -> case to of
    TBool    -> True
    TInt _   -> True
    TUInt _  -> True
    TFloat _ -> True
    TCReg _  -> True
    _        -> False
  TInt _ -> case to of
    TBool    -> True
    TInt _   -> True
    TUInt _  -> True
    TFloat _ -> True
    TCReg _  -> True
    _        -> False
  TUInt _ -> case to of
    TBool    -> True
    TInt _   -> True
    TUInt _  -> True
    TFloat _ -> True
    TCReg _  -> True
    _        -> False
  TFloat _ -> case to of
    TBool    -> True
    TInt _   -> True
    TUInt _  -> True
    TFloat _ -> True
    TAngle _ -> True
    _        -> False
  TAngle _ -> case to of
    TBool   -> True
    TAngle _-> True
    TCReg _ -> True
    _       -> False
  TCReg _ -> case to of
    TBool    -> True
    TInt _   -> True
    TUInt _ -> True
    TAngle _-> True
    TCReg _ -> True
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
unify :: ResolvedType -> ResolvedType -> Maybe ResolvedType
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
tcDecl _ = error "Unimplemented"

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

    Just (EType _ (TGate nC nQ)) -> do
      mods <- mapM tcModifier mods
      cargs <- mapM tcExprAs (TFloat Nothing) cargs
      qargs <- mapM tcAccessPath qargs
      case broadcast qargs of
        []      -> logMsg "Type error at (" ++ show loc ++ "): Gate arguments not broadcastable" >>
                   return $ SGateCall unitTy loc mods id cargs qargs
        [qargs] -> return $ SGateCall unitTy loc mods id cargs qargs
        [xs]    -> return $ SBlock unitTy $
                     [SGateCall unitTy loc mods id cargs qargs | qargs <- xs]

  where unitTy = EType TUnit False
    
-- | Broadcasting gate arguments
broadcast :: [AccessPath ElaboratedType] -> TC [AccessPath ElaboratedType]
broadcast _ = error "Unimplemented"

-- | Expression type checking
tcExpr :: Expr Location -> TC (Expr ElaboratedType)
tcExpr _ = error "Unimplemented"

-- | Type checks an expression as a particular type, inserting
--   a cast as needed
tcExprAs :: Expr Location -> ResolvedType -> TC (Expr ElaboratedType)
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
    True -> return $ ECast (exprType { ty = typ }) typ expr 

-- | Expression type checking
tcModifier :: Modifier Location -> TC (Modifier ElaboratedType)
tcModifier _ = error "Unimplemented"

-- | Access Path type checking
tcAccessPath :: AccessPath Location -> TC (AccessPath ElaboratedType)
tcAccessPath _ = error "Unimplemented"

-- | Resolves a type
resolveType :: Type Location -> TC ResolvedType
resolveType _ = error "Unimplemented"
