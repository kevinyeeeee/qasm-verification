{-|
Module      : Spec
Description : Specifications for openQASM 3
Copyright   : (c) Matthew Amy, 2025
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Frontend.OpenQASM3.Spec where

import Control.Monad

import Data.List

import Feynman.Core (ID)
import Feynman.Algebra.Base (Dyadic(..), DyadicRational, DMod2)

{- Term-level syntax for path sums -}

data BOp = Plus | Minus | Times | Div | Mod | Pow
         | LShift | RShift | LRot | RRot
         | Equal | LessThan | LessEq | GreaterThan | GreaterEq | And | Or
         deriving (Eq, Show)

data UOp = Neg | Wt | Exp | Sqrt deriving (Eq, Show)

-- | Classical types which can be in superposition
--
--   Register types are interpreted as unsigned integers
--   and can be dereferenced to get individual bits
--
--   The literals 0 and 1 are overloaded as both bits and
--   integers
data Type = Bit | Reg SExpr | UInt SExpr | Refined Type SExpr deriving (Eq, Show)

-- | L Values
data LVal = LVal ID (Maybe Int) deriving (Eq, Show)

-- | Sum-over-path expressions
data SExpr = Var ID (Maybe SExpr)
           | VarDec ID Type
           | ILit Int
           | BSLit String
           | RLit Double
           | Pi
           | BExp SExpr BOp SExpr
           | UExp UOp SExpr
           | Call ID [SExpr]
           -- Sum terms
           | Ket SExpr
           | Fun [(ID,Maybe Type)] SExpr
           | Sum [(ID,Maybe Type)] SExpr
           | Tensor SExpr SExpr
           | Compose SExpr SExpr
           | Dagger SExpr
           deriving (Eq, Show)

-- | Function. Special case of assertions
data Mapping = Mapping SExpr SExpr deriving (Eq,Show)

-- | Assertions. Conjunctions of assertions are represented as lists
data Assertion = Pointsto [SExpr] SExpr
               | Pure SExpr
               | Discard [SExpr]
               deriving (Eq, Show)

-- | Assertions in normal form
data NFAssertion = NFAssertion {
  qaps     :: [SExpr],
  qstate   :: SExpr,
  preds    :: SExpr,
  refines  :: SExpr,
  discards :: [SExpr]
  } deriving (Eq, Show)

-- | The empty assertion
emp :: NFAssertion
emp = NFAssertion [] (ILit 1) (ILit 1) (ILit 1) []

{- Transformations -}

-- | Normalizes all assertions
normalizeAssertions :: [Assertion] -> NFAssertion
normalizeAssertions = eraseRefinements . foldr go emp where
  go assrt nf = case assrt of
    Pointsto aps exprs ->
      if not (intersect aps (qaps nf ++ discards nf) == [])
      then error "Assertion references same qubit twice"
      else nf { qaps = aps ++ (qaps nf),
                qstate = if (qstate nf) == ILit 1 then exprs else Tensor exprs (qstate nf) }
    Pure expr   ->
      if (preds nf) == ILit 1
      then nf { preds = expr }
      else nf { preds = BExp expr And (preds nf) }
    Discard aps ->
      if not (intersect aps (qaps nf ++ discards nf) == [])
      then error "Assertion references same qubit twice"
      else nf { discards = aps ++ (discards nf) }

  eraseRefinements nf = case collectRefinements (qstate nf) of
    (qstate', Nothing) -> nf { qstate = qstate' }
    (qstate', Just p)  -> nf { qstate = Tensor qstate' p, refines = p }

-- | Maps a Boolean expression to a path sum
toPredicate :: SExpr -> SExpr
toPredicate exp = Sum [("%%%", Just Bit)] $ UExp Exp exponent where
  exponent = BExp (Var "%%%" Nothing) And (UExp Neg exp)

-- | Collects all refinements on free variables
collectRefinements :: SExpr -> (SExpr, Maybe SExpr)
collectRefinements = go where

  combineRefs r1 r2 = case (r1, r2) of
    (Just r1', Just r2') -> Just $ Tensor r1' r2'
    _                    -> mplus r1 r2

  collectRefs :: Maybe Type -> (Maybe Type, Maybe SExpr)
  collectRefs ty = case ty of
    Just (Refined ty exp) ->
      let (ty', refs) = collectRefs (Just ty) in
        (ty', combineRefs (Just $ toPredicate exp) refs)
    _               -> (ty, Nothing)

  processDecs :: [(ID, Maybe Type)] -> ([(ID, Maybe Type)], Maybe SExpr)
  processDecs xs = foldr processDec ([], Nothing) xs where
    processDec (id, ty) (xs,refs) =
      let (ty', refs') = collectRefs ty in
        ((id,ty'):xs, combineRefs refs refs')

  applyRef :: Maybe SExpr -> SExpr -> SExpr
  applyRef r exp = case r of
    Nothing  -> exp
    Just ref -> Tensor ref exp

  go sexpr = case sexpr of
    VarDec id ty  ->
      let (Just ty', refs) = collectRefs (Just ty) in
        (VarDec id ty', refs)
    BExp s1 op s2 ->
      let (s1', refs1) = go s1
          (s2', refs2) = go s2
      in
        (BExp s1' op s2', combineRefs refs1 refs2)
    UExp op s -> let (s', refs) = go s in (UExp op s', refs)
    Ket s -> let (s', refs) = go s in (Ket s', refs)
    Fun decs s ->
      let (s', refs)     = go s
          (decs', lrefs) = processDecs decs
      in
        (Fun decs' $ applyRef lrefs s', refs)
    Sum decs s ->
      let (s', refs)     = go s
          (decs', lrefs) = processDecs decs
      in
        (Sum decs' $ applyRef lrefs s', refs)
    Tensor s1 s2 ->
      let (s1', refs1) = go s1
          (s2', refs2) = go s2
      in
        (Tensor s1' s2', combineRefs refs1 refs2)
    Compose s1 s2 ->
      let (s1', refs1) = go s1
          (s2', refs2) = go s2
      in
        (Compose s1' s2', combineRefs refs1 refs2)
    Dagger s -> let (s', refs) = go s in (Dagger s', refs)
    _ -> (sexpr, Nothing)

{- Semantic checks -}

{- Parsing -}
{--

  ################### Abstract

  <expr> := <int> | <real> | <var>([<nat>])?
          | <uop> <expr>
          | <expr> <uop> <expr>
          | ( <expr> )
          | | <expr> >
          | fun <var>(:<type>)? -> <expr>
          | sum <var>(:<type>)? . <expr>
          | <expr> , <expr>
          | <expr> <expr>
          | <expr>`

  <uop>  := ! | ~ | - | popcount | exp | sqrt
  <bop>  := + | - | * | / | ^ | % | << | >> | <<< | >>>
  <type> := bit | bit[<expr>] | uint[<expr>]

  ################### Concrete

  <type> := bit | bit[<expr>] | uint[<expr>]

  <specification> := <exprs> --> <exprs>
                   | <assertions>
 
  <assertions> := <assertion>
                | <assertions> && <assertion>

  <assertion> := <sexprs> == <sexprs>

  <sexprs> := <sexpr>
            | <sexprs> , <sexpr>

  <sexpr> := <expr>
           | fun <decls> -> <sexpr>
           | sum { <decls> } . <sexpr>

  <expr> := <term>
          | <expr> + <term>
          | <expr> - <term>
          | <expr> % <term>

  <term> := <factor>
          | <term> * <factor>
          | <term> / <factor>
          | <term> ^ <factor>

  <factor> := <appl>
            | <factor> << <appl>
            | <factor> <<< <appl>
            | <factor> >> <appl>
            | <factor> >>> <appl>

  <appl> := <atom>
          | <appl> <atom>

  <atom> := <bool>
          | <nat>
          | <real>
          | pi
          | <id>
          | <id> [ <expr> ]
          | ( expr )
          | | <exprs> >
          | < <exprs> |
          | <atom>`
          | ! <atom>
          | ~ <atom>
          | - <atom>
          | <unary> ( <expr> )

  <decls> := <decl>
           | <decl> , <decls>

  <decl> := <var>
          | <var> : <type>

  <unary> := exp | popcount | sqrt

--}
