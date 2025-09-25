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
data ElaboratedType = EType { ty :: Type (),
                              const :: Bool
                            } deriving (Show)

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
log :: ErrMsg -> TC ()
log msg = modify (\env -> env { errs = errs env ++ [msg] })

-- | Looks up an identifier, beginning with the inner-most scope
getBinding :: ID -> TC (Maybe ElaboratedType)
getBinding x = do
  env <- get
  return . msum . map (Map.lookup x) $ scopes env ++ [constants env]


{- Semantic analysis & type checking -}

