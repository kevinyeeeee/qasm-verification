{-# LANGUAGE KindSignatures #-}

{-|
Module      : Core
Description : Core openQASM 3 syntax
Copyright   : (c) Matthew Amy, 2025
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Frontend.OpenQASM3.Core where

import Control.Monad
import Data.Complex
import Data.Bits
import Data.List
import Data.Maybe

import Feynman.Core (ID)
import qualified Feynman.Frontend.OpenQASM3.Syntax as S
import qualified Feynman.Frontend.OpenQASM3.Spec.Parser as SpecParser
import qualified Feynman.Frontend.OpenQASM3.Spec.Lexer as SpecLexer
import qualified Feynman.Frontend.OpenQASM3.Spec as Spec

{- Translation errors -}
data ErrMsg = Err String deriving Show

{- Convenience types -}
type Location   = S.SourceRef

data Annotation a = 
      Other (String,String)
    | Assert [(AccessPath a,Expr a)]
    | Fn (Expr a,Expr a)
    | Pre [(AccessPath a,Expr a)]
    | Post [(AccessPath a,Expr a)]
    | Triple [(AccessPath a, Expr a)] [(AccessPath a, Expr a)]
  deriving (Eq, Show)

type Version    = (Int, Maybe Int)

{- Core AST -}

-- | Type class for data annotated with an /a/
class Annotated (f :: * -> *) where
  getAnnotation :: f a -> a

-- | Unary operators
data UOp = SinOp
         | CosOp
         | TanOp
         | ArccosOp
         | ArcsinOp
         | ArctanOp
         | CeilOp
         | FloorOp
         | ExpOp
         | LnOp
         | SqrtOp
         | RealOp
         | ImOp
         | NegOp -- ~, !
         | UMinusOp -- -
         | PopcountOp -- popcount
         deriving (Eq, Show)

-- | Binary operators
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
           deriving (Eq, Show)


-- | OpenQASM 3 types. Arrays are currently unsupported
--
--   Parameterized by the type of type arguments
data TypeExpr' a = TCReg  a 
                 | TQBit          
                 | TQReg  a
                 -- Classical types
                 | TBool
                 | TUInt  (Maybe a)
                 | TInt   (Maybe a)
                 | TAngle (Maybe a)
                 | TFloat (Maybe a)
                 | TCmplx (Maybe a) -- Corresponds to openQASM 3 type cmplx[float[expr]]
                 -- Non-syntactic types
                 | TUnit
                 | TRange (TypeExpr' a)
                 | TGate { numCargs :: Int, numQargs :: Int }
                 | TProc { argTypes :: [TypeExpr' a], returnType :: Maybe (TypeExpr' a) }
                 deriving (Show, Eq)

type TypeExpr a = TypeExpr' (Expr a)
type Type       = TypeExpr' Int

-- | Promotes a type to a type expression, given a value for the annotation
asTypeExpr :: a -> Type -> TypeExpr a
asTypeExpr a typ = case typ of
  TCReg i        -> TCReg (EInt a i)
  TQBit          -> TQBit
  TQReg i        -> TQReg (EInt a i)
  TBool          -> TBool
  TUInt i        -> TUInt (fmap (EInt a) i)
  TInt  i        -> TInt (fmap (EInt a) i)
  TAngle i       -> TAngle (fmap (EInt a) i)
  TFloat i       -> TFloat (fmap (EInt a) i)
  TCmplx i       -> TCmplx (fmap (EInt a) i)
  TUnit          -> TUnit
  TRange t       -> TRange $ asTypeExpr a t
  TGate nc nq    -> TGate nc nq
  TProc args ret -> TProc (map (asTypeExpr a) args) (fmap (asTypeExpr a) ret)

-- | Classifies types as numeric
isNumeric :: TypeExpr' a -> Bool
isNumeric typeexpr = case typeexpr of
  TUInt  _      -> True
  TInt   _      -> True
  TFloat _      -> True
  TAngle _      -> True
  TCmplx _      -> True
  _             -> False

isQuantum :: TypeExpr' a -> Bool
isQuantum typeexpr = case typeexpr of
  TQReg _ -> True
  TQBit   -> True
  _       -> False

-- | Classifies types as bit-like
isBitvec :: TypeExpr' a -> Bool
isBitvec typeexpr = case typeexpr of
  TCReg i         -> True
  TBool           -> True
  TUInt  (Just i) -> True
  TInt   (Just i) -> True
  TAngle (Just i) -> True
  _               -> False

-- | Classifies types as comparable
isComparable :: TypeExpr' a -> Bool
isComparable typeexpr = case typeexpr of
  TCReg i       -> True
  TBool         -> True
  TUInt  _      -> True
  TInt   _      -> True
  TFloat _      -> True
  TAngle _      -> True
  _             -> False

-- | Classifies types as indexable
isIndexable :: Type -> Bool
isIndexable typ = case typ of
  TCReg _       -> True
  TQReg _       -> True
  TInt _        -> True
  TUInt _       -> True
  TAngle _      -> True
  _             -> False

-- | Access paths. Either a variable or an index into a register/bit array
data AccessPath a = AVar a ID
                  | AIndex a ID (Expr a)
                  deriving (Eq, Show)

instance Annotated AccessPath where
  getAnnotation (AVar a _) = a
  getAnnotation (AIndex a _ _) = a

-- | Promotes an access path to an equivalent expression
exprFromAP :: AccessPath a -> Expr a
exprFromAP (AVar a var) = EVar a var
exprFromAP (AIndex a var expr) = EIndex a (EVar a var) expr

-- | Gate modifiers
data Modifier a = MCtrl a Bool (Maybe (Expr a))
                | MInv a
                | MPow a (Expr a)
                deriving (Eq, Show)

instance Annotated Modifier where
  getAnnotation (MCtrl a _ _) = a
  getAnnotation (MInv a) = a
  getAnnotation (MPow a _) = a

-- | Expressions
data Expr a = EVar a ID
            | EIndex a (Expr a) (Expr a)
            | ECall a ID [(Expr a)]
            | EMeasure a (Expr a)
            | EInt a Int
            | EBits a [Bool]
            | EFloat a Double
            | ECmplx a (Complex Double)
            | ESlice a (Expr a) (Maybe (Expr a)) (Expr a) -- Inclusive on both ends
            | ESet a [(Expr a)]
            | EPi a
            | EIm a
            | EBool a Bool
            | EUOp a UOp (Expr a)
            | EBOp a (Expr a) BinOp (Expr a)
            | EStmt a (Stmt a)
            | ECast a (TypeExpr a) (Expr a)
            -- Spec only sum-over-path expresions
            | EVarDec a ID (TypeExpr a)
            | Ket a (Expr a)
            | Fun a [(ID,Maybe (TypeExpr a))] (Expr a)
            | Sum a [(ID,Maybe (TypeExpr a))] (Expr a)
            | Tensor a (Expr a) (Expr a)
            | Compose a (Expr a) (Expr a)
            | Dagger a (Expr a)
            deriving (Eq, Show)

instance Annotated Expr where
  getAnnotation expr = case expr of
    EVar a _ -> a
    EIndex a _ _ -> a
    ECall a _ _ -> a
    EMeasure a _ -> a
    EInt a _ -> a
    EBits a _ -> a
    EFloat a _ -> a
    ECmplx a _ -> a
    ESlice a _ _ _ -> a
    ESet a _ -> a
    EPi a -> a
    EIm a -> a
    EBool a _ -> a
    EUOp a _ _ -> a
    EBOp a _ _ _ -> a
    EStmt a _ -> a
    ECast a _ _ -> a
    Ket a _ -> a
    Tensor a _ _ -> a
    Sum a _ _ -> a

-- | Declarations
data Decl a =
    DVar { vid :: ID, typ :: TypeExpr a, val :: Maybe (Expr a), isConst :: Bool }
  | DDef { did :: ID, dparams :: [(ID, TypeExpr a)], dreturns :: Maybe (TypeExpr a), dbody :: Stmt a }
  | DGate { gid :: ID, gparams :: [(ID, TypeExpr a)], gqargs :: [ID], gbody :: Stmt a }
  | DExtern { eid :: ID, eparams :: [(TypeExpr a)], ereturns :: Maybe (TypeExpr a) }
  | DAlias { aid :: ID, aexps :: [(Expr a)] }
  deriving (Eq, Show)

-- | Statements
data Stmt a =
    SSkip a
  | SDeclare a (Decl a)
  | SBarrier a [AccessPath a]
  | SBlock a [Stmt a]
  | SExpr a (Expr a)
  | SGateCall a [Modifier a] ID [Expr a] [AccessPath a]
  | SAssign a (AccessPath a) (Expr a)
  | SFor a (ID, TypeExpr a) (Expr a) (Stmt a)
  | SBreak a
  | SContinue a
  | SEnd a
  | SIf a (Expr a) (Stmt a) (Stmt a)
  | SReset a (Expr a)
  | SReturn a (Maybe (Expr a))
  | SWhile a (Expr a) (Stmt a)
  | SAnnotated a [Annotation a] (Stmt a)
  | SPragma a String
  deriving (Eq, Show)

-- | Top level of an openQASM3 AST
data Prog a = Prog Version [Stmt a] deriving (Eq, Show)

{- Utilities -}

-- | Gets the identifier being declared
declID :: Decl a -> ID
declID decl = case decl of
  (DVar id _ _ _) -> id
  (DDef id _ _ _) -> id
  (DExtern id _ _) -> id
  (DAlias id _) -> id

-- | Applies a monadic computation to a list of nodes
inLst :: (S.ParseNode -> Either ErrMsg b) -> S.ParseNode -> Either ErrMsg [b]
inLst f S.NilNode            = return []
inLst f (S.Node S.List xs c) = mapM f xs
inLst f node                 = Left (Err $ "Fatal: malformed ast node (" ++ show node ++ ")")

{- Pretty printing -}


-- | Pretty prints the AST
prettyPrint :: Prog a -> [String]
prettyPrint (Prog (i,j) stmts) = [header] ++ concatMap prettyPrintStmt stmts where
  header = "OPENQASM " ++ show i ++ (maybe "" (("." ++) . show) j) ++ ";"

-- | Pretty prints a statement
prettyPrintStmt :: Stmt a -> [String]
prettyPrintStmt stmt = case stmt of
  SSkip _ -> [""]
  SDeclare _ decl -> prettyPrintDecl decl
  SBarrier _ xs -> ["barrier " ++ intercalate "," (map prettyPrintAP xs) ++ ";"]
  SBlock _ xs -> ["{"] ++ map ("  " ++) (concatMap prettyPrintStmt xs) ++ ["}"]
  SExpr _ expr -> [prettyPrintExpr expr ++ ";"]
  SGateCall _ mods id cargs qargs -> [m ++ " " ++ id ++ "(" ++ c ++ ")" ++ " " ++ q ++ ";"] where
    m = concatMap prettyPrintMod mods
    c = intercalate "," $ map prettyPrintExpr cargs
    q = intercalate "," $ map prettyPrintAP qargs
  SAssign _ ap expr -> [prettyPrintAP ap ++ " = " ++ prettyPrintExpr expr  ++ ";"]
  SFor _ (var, typ) expr stmt -> header:body ++ ["}"] where
    header = "for " ++ prettyPrintType typ ++ " " ++ var ++ " in " ++ prettyPrintExpr expr ++ "{"
    body = map ("  " ++) $ prettyPrintStmt stmt
  SBreak _ -> ["break;"]
  SContinue _ -> ["continue;"]
  SEnd _ -> ["end;"]
  SIf _ expr stmt stmt' -> ["if (" ++ e ++ ") {"] ++ i ++ ["} else {"] ++ el ++ ["}"] where
    e  = prettyPrintExpr expr
    i  = map ("  " ++) $ prettyPrintStmt stmt
    el = map ("  " ++) $ prettyPrintStmt stmt'
  SReset _ expr -> ["reset " ++ prettyPrintExpr expr ++ ";"]
  SReturn _ mexpr -> ["return " ++ (maybe "" prettyPrintExpr mexpr) ++ ";"] 
  SWhile _ expr stmt -> ["while (" ++ prettyPrintExpr expr ++ ") {"] ++ body ++ ["}"] where
    body = map ("  " ++) $ prettyPrintStmt stmt
  SAnnotated _ annots stmt -> map prettyPrintAnnotation annots ++ prettyPrintStmt stmt
  SPragma _ str -> ["pragma " ++ str]

prettyPrintAnnotation :: Annotation a -> String
prettyPrintAnnotation = error "TODO"

-- | Pretty prints a declaration
prettyPrintDecl :: Decl a -> [String]
prettyPrintDecl decl = case decl of 
  DVar var typ val isConstant -> [c ++ t ++ " " ++ var ++ init ++ ";"] where
    c = if isConstant then "const " else ""
    t = prettyPrintType typ
    init = maybe "" (\expr -> " = " ++ prettyPrintExpr expr) val
  DDef var params ret body -> ["def " ++ var ++ "(" ++ p ++ ")" ++ r ++ "{"] ++ b ++ ["}"] where
    p = intercalate "," . map (\(id,typ) -> prettyPrintType typ ++ " " ++ id) $ params
    r = maybe "" ((" -> " ++) . prettyPrintType) ret
    b = map ("  " ++) $ prettyPrintStmt body
  DGate var cp qp body -> ["gate " ++ var ++ "(" ++ p ++ ") " ++ q ++ "{"] ++ b ++ ["}"] where
    p = intercalate "," . map (\(id,typ) -> prettyPrintType typ ++ " " ++ id) $ cp
    q = intercalate "," qp
    b = map ("  " ++) $ prettyPrintStmt body
  DExtern var params ret -> ["extern " ++ var ++ "(" ++ p ++ ")" ++ r ++ ";"] where
    p = intercalate "," . map prettyPrintType $ params
    r = maybe "" ((" -> " ++) . prettyPrintType) ret
  DAlias var exprs -> ["let " ++ var ++ " = " ++ e ++ ";"] where
    e = intercalate " ++ " $ map prettyPrintExpr exprs

-- | Pretty prints an expression
prettyPrintExpr :: Expr a -> String
prettyPrintExpr expr = case expr of
  EVar _ var -> var
  EIndex _ expr idx -> prettyPrintExpr expr ++ "[" ++ prettyPrintExpr idx ++ "]"
  ECall _ var args -> var ++ "(" ++ intercalate "," (map prettyPrintExpr args) ++ ")"
  EMeasure _ expr -> "measure " ++ prettyPrintExpr expr
  EInt _ i   -> show i
  EBits _ xs -> "\"" ++ concatMap (\b -> if b then "1" else "0") xs ++ "\""
  EFloat _ r -> show r
  ECmplx _ c -> show c
  ESlice _ init step end -> "[" ++ prettyPrintExpr init ++ ":" ++ s ++ prettyPrintExpr end ++ "]"
    where s = maybe "" (\e -> prettyPrintExpr e ++ ":") step
  ESet _ exprs -> "{" ++ intercalate "," (map prettyPrintExpr exprs) ++ "}"
  EPi _ -> "pi"
  EIm _ -> "im"
  EBool _ b -> if b then "1" else "0"
  EUOp _ uop expr -> let e = prettyPrintExpr expr in case uop of
    SinOp      -> "sin(" ++ e ++ ")"
    CosOp      -> "cos(" ++ e ++ ")"
    TanOp      -> "tan(" ++ e ++ ")"  
    ArcsinOp   -> "arcsin(" ++ e ++ ")" 
    ArccosOp   -> "arccos(" ++ e ++ ")" 
    ArctanOp   -> "arctan(" ++ e ++ ")" 
    CeilOp     -> "ceil(" ++ e ++ ")" 
    FloorOp    -> "floor(" ++ e ++ ")" 
    ExpOp      -> "exp(" ++ e ++ ")" 
    LnOp       -> "log(" ++ e ++ ")" 
    SqrtOp     -> "sqrt(" ++ e ++ ")" 
    RealOp     -> "real(" ++ e ++ ")" 
    ImOp       -> "im(" ++ e ++ ")" 
    NegOp      -> "~" ++ e
    UMinusOp   -> "-" ++ e
    PopcountOp -> "popcount(" ++ e ++ ")"
  EBOp _ expr bop expr' -> case bop of
    AndOp    -> e ++ " & " ++ e'
    OrOp     -> e ++ " | " ++ e'
    XorOp    -> e ++ " ^ " ++ e'
    LShiftOp -> e ++ " << " ++ e'
    RShiftOp -> e ++ " >> " ++ e'
    LRotOp   -> "rotl(" ++ e ++ "," ++ e' ++ ")"
    RRotOp   -> "rotr(" ++ e ++ "," ++ e' ++ ")"
    EqOp     -> e ++ " == " ++ e'
    NEqOp    -> e ++ " != " ++ e'
    LTOp     -> e ++ " < " ++ e'
    LEqOp    -> e ++ " <= " ++ e'
    GTOp     -> e ++ " > " ++ e'
    GEqOp    -> e ++ " >= " ++ e'
    PlusOp   -> e ++ " + " ++ e'
    MinusOp  -> e ++ " - " ++ e'
    TimesOp  -> e ++ " * " ++ e'
    DivOp    -> e ++ " / " ++ e'
    ModOp    -> e ++ " % " ++ e'
    PowOp    -> e ++ " ** " ++ e'
    ConcatOp -> e ++ " ++ " ++ e'
    where e  = prettyPrintExpr expr
          e' = prettyPrintExpr expr'
  EStmt _ stmt -> concat $ prettyPrintStmt stmt
  ECast _ typexpr expr -> prettyPrintType typexpr ++ "(" ++ prettyPrintExpr expr ++ ")"

-- | Pretty prints an access path
prettyPrintAP :: AccessPath a -> String
prettyPrintAP ap = case ap of
  AVar _ var       -> var
  AIndex _ var idx -> var ++ "[" ++ prettyPrintExpr idx ++ "]"
  
-- | Pretty prints a gate modifier
prettyPrintMod :: Modifier a -> String
prettyPrintMod mod = case mod of 
  MCtrl _ neg mexpr -> mstr ++ argstr ++ " @ " where
    mstr = if neg then "negctrl" else "ctrl"
    argstr = case mexpr of
      Nothing -> ""
      Just expr -> "(" ++ prettyPrintExpr expr ++ ")"
  MInv _ -> "inv @ "
  MPow _ expr -> "pow(" ++ prettyPrintExpr expr ++ ") @ "

-- | Pretty prints a type expression
prettyPrintType :: TypeExpr a -> String
prettyPrintType typ = case typ of
  TCReg expr  -> "bit[" ++ prettyPrintExpr expr ++ "]"
  TQBit       -> "qubit"
  TQReg expr  -> "qubit[" ++ prettyPrintExpr expr ++ "]"
  TBool       -> "bool"
  TUInt expr  -> "uint" ++ printSize expr
  TInt expr   -> "int" ++ printSize expr
  TAngle expr -> "angle" ++ printSize expr
  TFloat expr -> "float" ++ printSize expr
  TCmplx expr -> "complex[float" ++ printSize expr ++ "]"
  TUnit       -> "unit"
  TRange ty   -> "range(" ++ prettyPrintType ty ++ ")"
  TGate nc nq -> "gate(" ++ show nc ++ "," ++ show nq ++ ")"
  TProc at rt -> let ret = maybe "unit" prettyPrintType rt in
    intercalate " -> " $ map prettyPrintType at ++ [ret]
  where printSize Nothing     = ""
        printSize (Just expr) = "[" ++ prettyPrintExpr expr ++ "]"

{- First translation to core AST -}

-- | Translation from concrete syntax to the core subset
qasmToCore :: S.ParseNode -> Either ErrMsg (Prog Location)
qasmToCore = translateProg

typeFromSpec :: a -> Spec.Type -> TypeExpr a
typeFromSpec x Spec.Bit = TBool
typeFromSpec x (Spec.Reg e) = TCReg (exprFromSpec x e)
typeFromSpec x (Spec.UInt e) = TUInt . Just $ exprFromSpec x e

accessPathFromSpec :: a -> Spec.SExpr -> AccessPath a
accessPathFromSpec x (Spec.Var i Nothing) = AVar x i
accessPathFromSpec x (Spec.Var i (Just e')) = AIndex x i (exprFromSpec x e')

exprFromSpec :: a -> Spec.SExpr -> Expr a
exprFromSpec = efs
  where
    efs x (Spec.Var i Nothing) = EVar x i
    efs x (Spec.Var i (Just e')) = EIndex x (EVar x i) (efs x e')
    efs x (Spec.VarDec i t) = EVarDec x i (typeFromSpec x t)
    efs x (Spec.ILit i) = EInt x i
    efs x (Spec.RLit r) = EFloat x r
    efs x (Spec.Pi) = EPi x
    efs x (Spec.BExp e1 b e2) = EBOp x (efs x e1) (bfs b) (efs x e2)
    efs x (Spec.UExp u e') = EUOp x (ufs u) (efs x e')
    efs x (Spec.Ket e') = Ket x (efs x e')
    efs x (Spec.Fun bindings e') = 
      Fun x (fmap (\(i,mt) -> (i,fmap (typeFromSpec x) mt)) bindings) (efs x e')
    efs x (Spec.Sum bindings e') = 
      Sum x (fmap (\(i,mt) -> (i,fmap (typeFromSpec x) mt)) bindings) (efs x e')
    efs x (Spec.Tensor e1 e2) = Tensor x (efs x e1) (efs x e2)
    efs x (Spec.Compose e1 e2) = Compose x (efs x e1) (efs x e2)
    efs x (Spec.Dagger e') = Dagger x (efs x e')

    bfs Spec.Plus = PlusOp
    bfs Spec.Minus = MinusOp
    bfs Spec.Times = TimesOp
    bfs Spec.Div = DivOp
    bfs Spec.Mod = ModOp
    bfs Spec.Pow = PowOp
    bfs Spec.LShift = LShiftOp
    bfs Spec.RShift = RShiftOp
    bfs Spec.LRot = LRotOp
    bfs Spec.RRot = RRotOp
    bfs Spec.Equal = EqOp
    bfs Spec.LessThan = LTOp
    bfs Spec.LessEq = LEqOp
    bfs Spec.GreaterThan = GTOp
    bfs Spec.GreaterEq = GEqOp
    bfs Spec.And = AndOp
    bfs Spec.Or = OrOp

    ufs Spec.Neg = NegOp
    ufs Spec.Wt = PopcountOp
    ufs Spec.Exp = ExpOp
    ufs Spec.Sqrt = SqrtOp

-- | Top-level translation
translateProg :: S.ParseNode -> Either ErrMsg (Prog Location)
translateProg node = case node of
  S.Node (S.Program i j _) xs _ -> mapM translateStmt xs >>= return . Prog (i,j)
  _  -> Left (Err $ "Fatal: malformed program node (" ++ show node ++ ")")

-- | Type translations
translateType :: S.ParseNode -> Either ErrMsg (TypeExpr Location)
translateType node = case node of
  S.Node S.BitTypeSpec [S.NilNode] c -> return $ TBool
  S.Node S.BitTypeSpec [exprnode] c -> translateExpr exprnode >>= return . TCReg

  S.Node S.IntTypeSpec [S.NilNode] c -> return $ TInt Nothing
  S.Node S.IntTypeSpec [exprnode] c  -> translateExpr exprnode >>= return . TInt . Just

  S.Node S.UintTypeSpec [S.NilNode] c -> return $ TUInt Nothing
  S.Node S.UintTypeSpec [exprnode] c -> translateExpr exprnode >>= return . TUInt . Just

  S.Node S.FloatTypeSpec [S.NilNode] c -> return $ TFloat Nothing
  S.Node S.FloatTypeSpec [exprnode] c  -> translateExpr exprnode >>= return . TFloat . Just

  S.Node S.AngleTypeSpec [S.NilNode] c -> return $ TAngle Nothing
  S.Node S.AngleTypeSpec [exprnode] c  -> translateExpr exprnode >>= return . TAngle . Just

  S.Node S.BoolTypeSpec _ c -> return $ TBool

  S.Node S.DurationTypeSpec _ c -> return $ TFloat Nothing

  S.Node S.StretchTypeSpec _ c -> return $ TFloat Nothing

  S.Node S.ComplexTypeSpec _ c -> return $ TCmplx Nothing

  S.Node S.CregTypeSpec [S.NilNode] c -> return $ TBool
  S.Node S.CregTypeSpec [exprnode] c -> translateExpr exprnode >>= return . TCReg

  S.Node S.QregTypeSpec [S.NilNode] c -> return $ TQBit
  S.Node S.QregTypeSpec [exprnode] c -> translateExpr exprnode >>= return . TQReg

  S.Node S.QubitTypeSpec [S.NilNode] c -> return $ TQBit
  S.Node S.QubitTypeSpec [exprnode] c -> translateExpr exprnode >>= return . TQReg

  S.Node S.ArrayTypeSpec _ c ->
    Left (Err "Array types unsupported")

  S.Node S.ReadonlyArrayRefTypeSpec _ c ->
    Left (Err "Array types unsupported")

  S.Node S.MutableArrayRefTypeSpec _ c ->
    Left (Err "Array types unsupported")

  _  -> Left (Err $ "Fatal: malformed type node (" ++ show node ++ ")")

-- | Identifier translations
translateIdent :: S.ParseNode -> Either ErrMsg ID
translateIdent node = case node of
  S.Node (S.Identifier id _) [] c -> return id

  _  -> Left (Err $ "Fatal: malformed identifier node (" ++ show node ++ ")")

-- | Access path translations
translateAccessPath :: S.ParseNode -> Either ErrMsg (AccessPath Location)
translateAccessPath node = case node of
  S.Node (S.HardwareQubit idx _) [] c -> return $ AVar c ("$" ++ show idx)

  S.Node (S.Identifier id _) [] c -> return $ AVar c id

  S.Node S.IndexedIdentifier [idnode, idxlist] c -> do
    id   <- translateIdent idnode
    idxs <- inLst translateExpr idxlist
    case idxs of
      [idx] -> return $ AIndex c id idx
      _     -> Left (Err "Array types unsupported")

  S.Node S.IndexExpr [idnode, idxlist] c -> do
    id   <- translateIdent idnode
    idxs <- inLst translateExpr idxlist
    case idxs of
      [idx] -> return $ AIndex c id idx
      _     -> Left (Err $ "Error at " ++ (S.pp_source c) ++ ": Multiple indices unsupported")

  _  -> Left (Err $ "Fatal: malformed access path node (" ++ show node ++ ")")

-- | Translation of Expressions
translateExpr :: S.ParseNode -> Either ErrMsg (Expr Location)
translateExpr node = case node of
  S.Node S.ParenExpr [exprnode] c -> translateExpr exprnode

  S.Node S.IndexExpr [exprnode, idxnode] c -> do
    expr <- translateExpr exprnode
    idxs  <- inLst translateExpr idxnode
    case idxs of
      [idx] -> return $ EIndex c expr idx
      _     -> Left (Err $ "Error at " ++ (S.pp_source c) ++ ": Multiple indices unsupported")

  S.Node (S.UnaryOperatorExpr uop) [exprnode] c -> do
    op   <- translateUOp uop
    expr <- translateExpr exprnode
    return $ EUOp c op expr

  S.Node (S.BinaryOperatorExpr bop) [leftnode, rightnode] c -> do
    op    <- translateBOp bop
    left  <- translateExpr leftnode
    right <- translateExpr rightnode
    return $ EBOp c left op right

  S.Node S.CastExpr [exprnode] c -> translateExpr exprnode

  S.Node S.DurationOfExpr [stmtnode] c -> do
    stmt <- translateStmt stmtnode
    return $ EStmt c stmt

  S.Node S.CallExpr [idnode, exprnodes] c -> do
    id    <- translateIdent idnode
    exprs <- inLst translateExpr exprnodes
    return $ ECall c id exprs

  S.Node S.ArrayInitExpr _ c ->
    Left (Err "Array types unsupported")

  S.Node S.SetInitExpr exprs c -> do
    mapM translateExpr exprs >>= return . (ESet c)

  S.Node S.RangeInitExpr [beginnode, stepnode, endnode] c -> do
    begin <- translateExpr beginnode
    step <- case stepnode of
      S.NilNode -> return Nothing
      node      -> liftM Just $ translateExpr stepnode
    end <- translateExpr endnode
    return $ ESlice c begin step end

  S.Node S.DimExpr [expr] c -> 
    Left (Err "Array types unsupported")

  S.Node S.MeasureExpr [exprnode] c -> do
    expr <- translateExpr exprnode
    return $ EMeasure c expr

  S.Node (S.Identifier id _) [] c -> return $ EVar c id

  S.Node (S.IntegerLiteral i _) [] c -> return $ EInt c (fromInteger i)

  S.Node (S.FloatLiteral r _) [] c -> return $ EFloat c r

  S.Node (S.ImaginaryLiteral r _) [] c -> return $ ECmplx c (0 :+ r)

  S.Node (S.BooleanLiteral b _) [] c -> return $ EBool c b

  S.Node (S.BitstringLiteral xs _) [] c -> return $ EBits c xs

  S.Node (S.TimingLiteral _ _) [] c -> return $ EInt c 0

  S.Node (S.HardwareQubit i _) [] c -> return $ EVar c ("#" ++ show i)

  S.Node S.IndexedIdentifier [idnode, idxlist] c -> do
    id   <- translateIdent idnode
    idxs <- inLst translateExpr idxlist
    case idxs of
      [idx] -> return $ EIndex c (EVar c id) idx
      _     -> Left (Err "Array types unsupported")

  S.Node S.CastExpr [typenode, exprnode] c -> do
    typ  <- translateType typenode
    expr <- translateExpr exprnode
    return $ ECast c typ expr

  _  -> Left (Err $ "Fatal: malformed expression node (" ++ show node ++ ")")

  where intOfBitstring xs =
          foldr (+) 0 . map (\(b,i) -> if b then shift 1 i else 0) $ zip xs [0..]

-- | Translation of gate modifiers
translateModifier :: S.ParseNode -> Either ErrMsg (Modifier Location)
translateModifier node = case node of
  S.Node S.PowGateModifier [exprnode] c -> do
    expr <- translateExpr exprnode
    return $ MPow c expr

  S.Node S.InvGateModifier [] c -> return $ MInv c

  S.Node S.CtrlGateModifier [S.NilNode] c -> return $ MCtrl c False Nothing
  S.Node S.CtrlGateModifier [exprnode] c -> do
    expr <- translateExpr exprnode
    return $ MCtrl c False (Just expr)

  S.Node S.NegCtrlGateModifier [S.NilNode] c -> return $ MCtrl c True Nothing
  S.Node S.NegCtrlGateModifier [exprnode] c -> do
    expr <- translateExpr exprnode
    return $ MCtrl c True (Just expr)

  _  -> Left (Err $ "Fatal: malformed modifier node (" ++ show node ++ ")")

translateAnnotations :: [S.ParseNode] -> Either ErrMsg [Annotation S.SourceRef]
translateAnnotations nodes = case nodes of
  (S.Node (S.Annotation "pre" str _) [] c):
    (S.Node (S.Annotation "post" str' _) [] c'):
    ns ->
      let preAssertions  = SpecParser.parseAssertion . SpecLexer.lexer $ str
          postAssertions = SpecParser.parseAssertion . SpecLexer.lexer $ str' in do
        rest <- translateAnnotations ns
        return $ Triple (translateAssertions c preAssertions) (translateAssertions c postAssertions) : rest
  node:ns -> do
    annot <- translateAnnotation node
    rest <- translateAnnotations ns
    return $ annot : rest
  [] -> return []
  where 
    translateAssertions c assertions = 
      fmap ((\(Spec.Equals e1 e2) -> (accessPathFromSpec c e1,exprFromSpec c e2)) . Spec.eraseRefinements) assertions

-- | Translation of Annotations
translateAnnotation :: S.ParseNode -> Either ErrMsg (Annotation S.SourceRef)
translateAnnotation node = case node of
  S.Node (S.Annotation "assert" str _) [] c -> 
    let assertions = SpecParser.parseAssertion (SpecLexer.lexer str) in
    Right (Assert (translateAssertions c assertions))
  S.Node (S.Annotation "fn" str _) [] c -> return (Fn (error "TODO"))
  S.Node (S.Annotation a str _) [] c -> return (Other (a,str))
  _  -> Left (Err $ "Fatal: malformed annotation node (" ++ show node ++ ")")
  where 
    translateAssertions c assertions = 
      fmap ((\(Spec.Equals e1 e2) -> (accessPathFromSpec c e1,exprFromSpec c e2)) . Spec.eraseRefinements) assertions


-- | Translation of Arguments
translateArg :: S.ParseNode -> Either ErrMsg (ID, TypeExpr Location)
translateArg node = case node of
  S.Node S.ArgumentDefinition [typespec, idnode] c -> do
    typ <- translateType typespec
    id <- translateIdent idnode
    return $ (id, typ)

  _  -> Left (Err $ "Fatal: malformed argument node (" ++ show node ++ ")")

-- | Translation of statements
translateStmt :: S.ParseNode -> Either ErrMsg (Stmt Location)
translateStmt node = case node of
  S.NilNode -> return $ SSkip S.NilRef
  
  S.Node (S.Pragma str _) [] c -> return $ SPragma c str

  S.Node S.Statement [stmt] c -> translateStmt stmt

  S.Node S.Statement (stmt:xs) c -> do
    annots <- translateAnnotations xs
    s <- translateStmt stmt
    return $ SAnnotated c annots s

  S.Node S.Scope stmts c -> do
    mapM translateStmt stmts >>= return . SBlock c

  S.Node S.AliasDeclStmt (idnode:exprnodes) c -> do
    id <- translateIdent idnode
    exprs <- mapM translateExpr exprnodes
    return $ SDeclare c (DAlias id exprs)

  S.Node (S.AssignmentStmt op) [idnode, exprnode] c -> do
    idexpr <- translateAccessPath idnode
    expr <- translateExpr exprnode
    assop <- translateCompoundAOp op
    case assop of
      Nothing  -> return $ SAssign c idexpr expr
      Just bop -> return $ SAssign c idexpr (EBOp c (exprFromAP idexpr) bop expr)

  S.Node (S.BarrierStmt) idnodes c -> do
    idexprs <- mapM translateAccessPath idnodes
    return $ SBarrier c idexprs

  S.Node S.BoxStmt [_, scope@(S.Node S.Scope _ _)] _ -> translateStmt scope

  S.Node S.BreakStmt [] c -> return $ SBreak c

  S.Node (S.CalStmt _) [] c -> return $ SSkip c
  S.Node (S.DefcalgrammarStmt _ _) [] c -> return $ SSkip c

  S.Node S.ClassicalDeclStmt [typespec, idnode, initexpr] c -> do
    ty <- translateType typespec
    id <- translateIdent idnode
    expr <- case initexpr of
      S.NilNode -> return Nothing
      node -> liftM Just $ translateExpr node
    return $ SDeclare c (DVar id ty expr False)

  S.Node S.ConstDeclStmt [typespec, idnode, initexpr] c -> do
    ty <- translateType typespec
    id <- translateIdent idnode
    expr <- translateExpr initexpr
    return $ SDeclare c (DVar id ty (Just expr) True)

  S.Node S.ContinueStmt [] c   -> return $ SContinue c

  S.Node S.DefStmt [idnode, argnodes, rettype, stmt] c -> do
    id <- translateIdent idnode
    args <- inLst translateArg argnodes
    ret <- case rettype of
      S.NilNode -> return Nothing
      node -> liftM Just $ translateType node
    body <- translateStmt stmt
    return $ SDeclare c (DDef id args ret body)

  S.Node S.DefcalStmt _ c -> return $ SSkip c

  S.Node S.DelayStmt _ c -> return $ SSkip c

  S.Node S.EndStmt [] c -> return $ SEnd c

  S.Node S.ExpressionStmt [exprnode] c -> 
    translateExpr exprnode >>= return . SExpr c

  S.Node S.ExternStmt [idnode, typenodes, rettype] c -> do
    id <- translateIdent idnode
    types <- inLst translateType typenodes
    ret <- case rettype of
      S.NilNode -> return Nothing
      node -> liftM Just $ translateType node
    return $ SDeclare c (DExtern id types ret)

  S.Node S.ForStmt [typenode, idnode, exprnode, stmtnode] c -> do
    typ <- translateType typenode
    id <- translateIdent idnode
    expr <- translateExpr exprnode
    body <- translateStmt stmtnode
    return $ SFor c (id, typ) expr body

  S.Node S.GateStmt [idnode, cargnodes, qargnodes, stmt] c -> do
    id <- translateIdent idnode
    cargs <- case cargnodes of
      S.NilNode -> return []
      node -> inLst translateIdent node
    qargs <- inLst translateIdent qargnodes
    body <- translateStmt stmt
    let args = zip cargs (repeat (TAngle Nothing))
    return $ SDeclare c (DGate id args qargs body)

  S.Node S.GateCallStmt [modnodes, idnode, paramnodes, _, argnodes] c -> do
    modifiers <- inLst translateModifier modnodes
    id <- translateIdent idnode
    params <- inLst translateExpr paramnodes
    args <- inLst translateAccessPath argnodes
    return $ SGateCall c modifiers id params args
    
  S.Node S.IfStmt [condnode, thennode, elsenode] c -> do
    cond <- translateExpr condnode
    thn <- translateStmt thennode
    els <- translateStmt elsenode
    return $ SIf c cond thn els

  S.Node (S.IncludeStmt path _) [] c -> return $ SSkip c
    --Left (Err $ "Error at " ++ (S.pp_source c) ++ ": include unsupported")

  S.Node S.InputIoDeclStmt [typenode, idnode] c -> do
    ty <- translateType typenode
    id <- translateIdent idnode
    return $ SDeclare c (DVar id ty Nothing False)

  S.Node S.OutputIoDeclStmt [typenode, idnode] c -> do
    ty <- translateType typenode
    id <- translateIdent idnode
    return $ SDeclare c (DVar id ty Nothing False)

  S.Node S.MeasureArrowAssignmentStmt [srcexpr, S.NilNode] c -> do
    src <- translateExpr srcexpr
    return $ SExpr c src

  S.Node S.MeasureArrowAssignmentStmt [srcexpr, tgtexpr] c -> do
    src <- translateExpr srcexpr
    tgt <- translateAccessPath tgtexpr
    return $ SAssign c tgt src

  S.Node S.CregOldStyleDeclStmt [idnode, exprnode] c -> do
    id <- translateIdent idnode
    case exprnode of
      S.NilNode -> return $ SDeclare c (DVar id TBool Nothing False)
      node      -> do
        expr <- translateExpr node
        return $ SDeclare c (DVar id (TCReg expr) Nothing False)

  S.Node S.QregOldStyleDeclStmt [idnode, exprnode] c -> do
    id <- translateIdent idnode
    case exprnode of
      S.NilNode -> return $ SDeclare c (DVar id TQBit Nothing False)
      node -> do
        expr <- translateExpr node
        return $ SDeclare c (DVar id (TQReg expr) Nothing False)

  S.Node S.QuantumDeclStmt [typenode, idnode] c -> do
    id <- translateIdent idnode
    typ <- translateType typenode
    return $ SDeclare c (DVar id typ Nothing False)

  S.Node (S.ResetStmt) [exprnode] c -> do
    expr <- translateExpr exprnode
    return $ SReset c expr

  S.Node S.ReturnStmt [exprnode] c -> do
    case exprnode of
      S.NilNode -> return $ SReturn c Nothing
      node -> do
        expr <- translateExpr node
        return $ SReturn c (Just expr)

  S.Node S.WhileStmt [condnode, bodynode] c -> do
    cond <- translateExpr condnode
    body <- translateStmt bodynode
    return $ SWhile c cond body

  _  -> Left (Err $ "Fatal: malformed statement node (" ++ show node ++ ")")

-- | Translation of unary operators
translateUOp :: S.Token -> Either ErrMsg UOp
translateUOp token = case token of
  S.MinusToken                -> return UMinusOp
  S.TildeToken                -> return NegOp
  S.ExclamationPointToken     -> return NegOp
  S.PopcountToken             -> return PopcountOp

-- | Translation of binary operators
translateBOp :: S.Token -> Either ErrMsg BinOp
translateBOp token = case token of
  S.PlusToken                   -> return PlusOp
  S.DoublePlusToken             -> return ConcatOp
  S.MinusToken                  -> return MinusOp
  S.AsteriskToken               -> return TimesOp
  S.DoubleAsteriskToken         -> return PowOp
  S.SlashToken                  -> return DivOp
  S.PercentToken                -> return ModOp
  S.PipeToken                   -> return OrOp
  S.DoublePipeToken             -> return OrOp
  S.AmpersandToken              -> return AndOp
  S.DoubleAmpersandToken        -> return AndOp
  S.CaretToken                  -> return XorOp
  S.LessToken                   -> return LTOp
  S.LessEqualsToken             -> return LEqOp
  S.GreaterToken                -> return GTOp
  S.GreaterEqualsToken          -> return GEqOp
  S.DoubleLessToken             -> return LShiftOp
  S.DoubleGreaterToken          -> return RShiftOp
  S.ExclamationPointEqualsToken -> return NEqOp
  S.DoubleEqualsToken           -> return EqOp
  _                             -> error $ "Unexpected operator token " ++ show token

-- | Translation of compound assignment operators
translateCompoundAOp :: S.Token -> Either ErrMsg (Maybe BinOp)
translateCompoundAOp token = case token of
  S.EqualsToken               -> return Nothing
  S.PlusEqualsToken           -> return $ Just PlusOp
  S.MinusEqualsToken          -> return $ Just MinusOp
  S.AsteriskEqualsToken       -> return $ Just TimesOp
  S.SlashEqualsToken          -> return $ Just DivOp
  S.AmpersandEqualsToken      -> return $ Just AndOp
  S.PipeEqualsToken           -> return $ Just OrOp
  S.CaretEqualsToken          -> return $ Just XorOp
  S.DoubleLessEqualsToken     -> return $ Just LShiftOp
  S.DoubleGreaterEqualsToken  -> return $ Just RShiftOp
  S.PercentEqualsToken        -> return $ Just ModOp
  S.DoubleAsteriskEqualsToken -> return $ Just PowOp
