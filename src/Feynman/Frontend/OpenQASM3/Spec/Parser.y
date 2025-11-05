{
  module Feynman.Frontend.OpenQASM3.Spec.Parser(parseAssertion,parseSExpr) where

import Feynman.Frontend.OpenQASM3.Spec.Lexer
import qualified Feynman.Frontend.OpenQASM3.Spec.Lexer as L
import Feynman.Frontend.OpenQASM3.Spec
}

%name parseFunction function
%name parseAssertion assertions
%name parseSExpr sexpr
%tokentype { Token }
%error { parseError }

%token
  
  bit      { TBit }
  bits     { TBitstring $$ }
  uint     { TUInt }
  pi       { TPi }
  popcount { TPopcount }
  exp      { TExp }
  sqrt     { TSqrt }
  disc     { TDiscard }
  fun      { TFun }
  sum      { TSum }
  '~'      { TNeg }
  '+'      { TPlus }
  '-'      { TMinus }
  '*'      { TTimes }
  '/'      { TDiv }
  '^'      { TPow }
  '%'      { TMod }
  lshift   { TLShift }
  rshift   { TRShift }
  lrot     { TLRot }
  rrot     { TRRot }
  arrow    { TArrow }
  mapsto   { TLongArrow }
  '('      { TLParen }
  ')'      { TRParen }
  '{'      { TLBrace }
  '}'      { TRBrace }
  '['      { TLBracket }
  ']'      { TRBracket }
  '<'      { TLAngle }
  '>'      { TRAngle }
  leq      { TLAngleEq }
  geq      { TRAngleEq }
  '|'      { TBar }
  ':'      { TColon }
  ','      { TComma }
  '.'      { TDot }
  "~>"     { TPointsto }
  "=="     { TEquals }
  neq      { TNEquals }
  "&&"     { TAnd }
  or       { TOr }
  '`'      { TBacktick }
  id       { TID   $$ }
  real     { TReal $$ }
  int      { TInt  $$ }

%%

type : basetype '{' pred '}' { Refined $1 $3 }
     | basetype              { $1 }

basetype : bit               { Bit }
         | bit '[' expr ']'  { Reg $3 }
         | uint '[' expr ']' { UInt $3 }

function : sexpr mapsto sexpr { Mapping $1 $3 }

assertions : assertion                { [$1] }
           | assertions ',' assertion { $1 ++ [$3] }

assertion : expr "~>" sexpr          { Pointsto [$1] $3 }
          | '(' exprs ')' "~>" sexpr { Pointsto $2 $5 }
          | disc expr                { Discard [$2] }
          | disc '(' exprs ')'       { Discard $3 }
          | pred                     { Pure $1 }

sexpr : sexpr1        { $1 }
      | sexpr sexpr1  { Tensor $1 $2 }

sexpr1 : sexpr2             { $1 }
       | sexpr1 '+' sexpr2  { BExp $1 Plus $3 }

sexpr2 : sexpr3            { $1 }
       | sexpr2 '.' sexpr3 { BExp $1 Times $3 }

sexpr3 : expr                        { $1 }
       | fun decls arrow sexpr       { Fun $2 $4 }
       | sum '{' decls '}' '.' sexpr { Sum $3 $6 }
       | '|' exprs '>'               { foldl1 Tensor $ map Ket $2 }
       | '<' exprs '|'               { Dagger (foldl1 Tensor $ map Ket $2) }
       | sexpr3 '`'                  { Dagger $1 }
       | '(' sexpr ')'               { $2 }

exprs : expr           { [$1] }
      | exprs ',' expr { $1 ++ [$3] }

expr : expr1          { $1 }
     | expr '+' expr1 { BExp $1 Plus $3 }
     | expr '-' expr1 { BExp $1 Minus $3 }
     | expr '%' expr1 { BExp $1 Mod $3 }
     | expr or expr1  { BExp $1 Or $3 }

expr1 : expr2            { $1 }
      | expr1 '*' expr2  { BExp $1 Times $3 }
      | expr1 '/' expr2  { BExp $1 Div $3 }
      | expr1 '^' expr2  { BExp $1 Pow $3 }
      | expr1 "&&" expr2 { BExp $1 And $3 }

expr2 : expr3              { $1 } 
      | expr2 lshift expr3 { BExp $1 LShift $3 }
      | expr2 lrot expr3   { BExp $1 LRot $3 }
      | expr2 rshift expr3 { BExp $1 RShift $3 }
      | expr2 rrot expr3   { BExp $1 RRot $3 }

expr3 : int                  { ILit $1 }
      | bits                 { BSLit $1 }
      | real                 { RLit $1 }
      | pi                   { Pi }
      | id                   { Var $1 Nothing }
      | id '[' expr ']'      { Var $1 (Just $3) }
      | id ':' type          { VarDec $1 $3 }
      | '(' expr ')'         { $2 }
      | '~' expr3            { UExp Neg $2 }
      | '-' expr3            { UExp Neg $2 }
      | unary '(' expr ')'   { UExp $1 $3 }
      | id '(' exprs ')'     { Call $1 $3 }

pred : pred1          { $1 }      
     | pred or pred1  { BExp $1 Or $3 }

pred1 : pred2            { $1 }
      | pred1 "&&" pred2 { BExp $1 And $3 }

pred2 : pred3              { $1 }
      | pred2 "==" pred3   { BExp $1 Equal $3 }
      | pred2 neq pred3    { UExp Neg (BExp $1 Equal $3) }
      | pred2 '<' pred3    { BExp $1 LessThan $3 }
      | pred2 leq pred3    { BExp $1 LessEq $3 }
      | pred2 '>' pred3    { BExp $1 GreaterThan $3 }
      | pred2 geq pred3    { BExp $1 GreaterEq $3 }

pred3 : expr               { $1 }

decls : decl { [$1] }
      | decl ',' decls { ($1:$3) }

decl : id                   { ($1, Nothing) }
     | id ':' type          { ($1, Just $3) }

unary : popcount { Wt }
      | exp      { Exp }
      | sqrt     { Sqrt }

{

parseError :: [Token] -> a
parseError xs = error $ "Parse error: " ++ concatMap show xs

-- vim: ft=haskell
}
