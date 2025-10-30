{
  module Feynman.Frontend.OpenQASM3.Spec.Parser(parseAssertion,parseSExpr) where

import Feynman.Frontend.OpenQASM3.Spec.Lexer
import qualified Feynman.Frontend.OpenQASM3.Spec.Lexer as L
import Feynman.Frontend.OpenQASM3.Spec
}

%name parseAssertion assertions
%name parseSExpr sexprs
%tokentype { Token }
%error { parseError }

%token
  
  bit      { TBit }
  uint     { TUInt }
  pi       { TPi }
  popcount { TPopcount }
  exp      { TExp }
  sqrt     { TSqrt }
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
  '='      { TEquals }
  neq      { TNEquals }
  '&'      { TAnd }
  or       { TOr }
  '`'      { TBacktick }
  id       { TID   $$ }
  real     { TReal $$ }
  int      { TInt  $$ }

%%

type : basetype '|' refinement { Refined $1 $3 }
     | basetype                { $1 }

basetype : bit               { Bit }
         | bit '[' expr ']'  { Reg $3 }
         | uint '[' expr ']' { UInt $3 }

assertions : assertion                { [$1] }
           | assertions '&' assertion { $1 ++ [$3] }

assertion : sexprs '=' sexprs { Equals $1 $3 }

sexprs : sexpr            { $1 }
       | '(' sexprs ')'    { $2 }
       | sexprs ',' sexpr { Tensor $1 $3 }

sexpr : expr                        { $1 }
      | fun decls arrow sexpr       { Fun $2 $4 }
      | sum '{' decls '}' '.' sexpr { Sum $3 $6 }

refinement : refinement1               { $1 }
           | refinement or refinement1 { BExp $1 Or $3 }

refinement1 : refinement2                 { $1 }
            | refinement1 '&' refinement2 { BExp $1 And $3 }

refinement2 : refinement3        { $1 }
            | '~' refinement3    { UExp Neg $2 }

refinement3 : '(' refinement ')' { $2 }
            | expr '=' expr      { BExp $1 Equal $3 }
            | expr neq expr      { UExp Neg (BExp $1 Equal $3) }
            | expr '<' expr      { BExp $1 LessThan $3 }
            | expr leq expr      { BExp $1 LessEq $3 }
            | expr '>' expr      { BExp $1 GreaterThan $3 }
            | expr geq expr      { BExp $1 GreaterEq $3 }

expr : term          { $1 }
     | sexprs '+' sexprs { BExp $1 Plus $3 }
     | expr '-' term { BExp $1 Minus $3 }
     | expr '%' term { BExp $1 Mod $3 }
     | expr or term { BExp $1 Or $3 }

term : factor          { $1 }
     | term '*' factor { BExp $1 Times $3 }
     | term '/' factor { BExp $1 Div $3 }
     | term '^' factor { BExp $1 Pow $3 }
     | term '&' factor { BExp $1 And $3 }

factor : appl               { $1 } 
       | factor lshift appl { BExp $1 LShift $3 }
       | factor lrot appl   { BExp $1 LRot $3 }
       | factor rshift appl { BExp $1 RShift $3 }
       | factor rrot appl   { BExp $1 RRot $3 }

appl : atom      { $1 }
     | appl atom { Compose $1 $2 }

atom : int                { ILit $1 }
     | real               { RLit $1 }
     | pi                 { Pi }
     | id                 { Var $1 Nothing }
     | id '[' expr ']'    { Var $1 (Just $3) }
     | id ':' type        { VarDec $1 $3 }
     | '(' expr ')'       { $2 }
     | '|' sexprs '>'     { Ket $2 }
     | '<' sexprs '|'     { Dagger (Ket $2) }
     | atom '`'           { Dagger $1 }
     | '~' atom           { UExp Neg $2 }
     | '-' atom           { UExp Neg $2 }
     | unary '(' expr ')' { UExp $1 $3 }

decls : decl { [$1] }
      | decl ',' decls { ($1:$3) }

decl : id          { ($1, Nothing) }
     | id ':' type { ($1, Just $3) }

unary : popcount { Wt }
      | exp      { Exp }
      | sqrt     { Sqrt }

{

parseError :: [Token] -> a
parseError xs = error $ "Parse error: " ++ concatMap show xs

-- vim: ft=haskell
}
