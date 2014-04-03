{
module HW6parse where
import Prelude hiding (LT, GT, EQ, id)
import Data.Char
import HW6
import Lexer
}

%name parser
%tokentype { Token }

%token 
    function { TokenKeyword "fun" }
    if    { TokenKeyword "if" }
    then  { TokenKeyword "then" }
    else  { TokenKeyword "else" }
    true  { TokenKeyword "true" }
    false { TokenKeyword "false" }
    let   { TokenKeyword "let" }
    in    { TokenKeyword "in" }
    id    { TokenIdent $$ }
    digits { Digits $$ }
    '='    { Symbol "=" }
    '+'    { Symbol "+" }
    '-'    { Symbol "-" }
    '*'    { Symbol "*" }
    '/'    { Symbol "/" }
    '<'    { Symbol "<" }
    '>'    { Symbol ">" }
    '<='   { Symbol "<=" }
    '>='   { Symbol ">=" }
    '=='   { Symbol "==" }
    '&&'   { Symbol "&&" }
    '!'    { Symbol "!" }
    '||'   { Symbol "||" }
    '('    { Symbol "(" }
    ')'    { Symbol ")" }

%left '||'
%left '&&'
%left '=='  '<' '>' '<='  '>='
%left '+' '-'
%left '*' '/'
%left CALL
%left NEG

%%

Exp : function '(' id ')' Exp  { Function $3 $5 }
    | let id '=' Exp in Exp           { Declare $2 $4 $6 }
    | if Exp then Exp else Exp  { If $2 $4 $6 }
    | Or                               { $1 }

Or   : Or '||' And        { Binary Or $1 $3 }
     | And                { $1 }

And   : And '&&' Comp      { Binary And $1 $3 }
     | Comp                { $1 }

Comp : Comp '==' Term     { Binary EQ $1 $3 }
     | Comp '<' Term      { Binary LT $1 $3 }
     | Comp '>' Term      { Binary GT $1 $3 }
     | Comp '<=' Term     { Binary LE $1 $3 }
     | Comp '>=' Term     { Binary GE $1 $3 }
     | Term               { $1 }

Term : Term '+' Factor    { Binary Add $1 $3 }
     | Term '-' Factor    { Binary Sub $1 $3 }
     | Factor             { $1 }

Factor : Factor '*' Primary    { Binary Mul $1 $3 }
       | Factor '/' Primary    { Binary Div $1 $3 }
       | Primary               { $1 }

Primary : Primary Primary  %prec CALL  { Call $1 $2 }
        | digits         { Literal (IntV $1) }
        | true           { Literal (BoolV True) }
        | false          { Literal (BoolV False) }
        | '-' Primary %prec NEG   { Unary Neg $2 }
        | '!' Primary %prec NEG   { Unary Not $2 }
        | id             { Variable $1 }
        | '(' Exp ')'    { $2 }

{

symbols = ["+", "-", "*", "/", "(", ")", "==", "=", "<=", ">=", "<", ">", "||", "&&", "!"]
keywords = ["fun", "let", "if", "in", "then", "else", "true", "false"]
parseExp str = parser (lexer symbols keywords str)

parseInput = do
  input <- getContents
  print (parseExp input)

}
