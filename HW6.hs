module HW6 where

import Prelude hiding (LT, GT, EQ, id)
import Data.Maybe
import Data.List

data BinaryOp = Add | Sub | Mul | Div | And | Or
              | GT | LT | LE | GE | EQ
  deriving (Eq, Show)

data UnaryOp = Neg | Not
  deriving (Eq, Show)

data Value = IntV  Int
           | BoolV Bool
           | ClosureV String Exp Env  -- new
  deriving (Eq)

instance Show Value where
	show (IntV n) = show n
	show (BoolV b) = show b
	show (ClosureV x b env) = "<Closure " ++ x ++ ">"

data Exp = Literal   Value
         | Unary     UnaryOp Exp
         | Binary    BinaryOp Exp Exp
         | If        Exp Exp Exp
         | Variable  String
         | Declare   String Exp Exp
         | Function  String Exp      -- new
         | Call      Exp Exp         -- changed
  deriving (Eq)
  
type Env = [(String, Value)]

getNewVar :: Int -> String
getNewVar nextVal = "X" ++ show(nextVal)

infer :: Exp -> Type
infer e = applySigma (unify (getConstraints e)) (TVar "X3")

applySigma :: [(String, Type)] -> Type -> Type
applySigma [] t' = t'
applySigma ((s,t):sig) t' = applySigma sig (subst s t t')

getConstraints :: Exp -> [(Type, Type)]
getConstraints (Literal (IntV _)) = let ix = getNewVar 1 in [(TVar ix, TInt)]
getConstraints (Literal (BoolV _)) = let bx = getNewVar 2 in [(TVar bx, TBool)]
getConstraints (Unary (Not) e) = let ux = getNewVar 3 in
                                    let ((ex,t):c) = getConstraints e in
                                        [(TVar ux, TBool), (t, TBool), (ex, t)] ++ c
getConstraints (Unary (Neg) e) = let ux = getNewVar 4 in
                                    let ((ex,t):c) = getConstraints e in
                                        [(TVar ux, TInt), (t, TInt), (ex, t)] ++ c
getConstraints (Binary (Add) e1 e2) = let bx = getNewVar 5 in
                                        let ((e1x, t1):c1, (e2x, t2):c2) = (getConstraints e1, getConstraints e2) in
                                            [(TVar bx, TInt), (t1, TInt), (t2, TInt), (e1x, t1), (e2x, t2)] ++ c1 ++ c2
getConstraints (Binary (Sub) e1 e2) = let bx = getNewVar 6 in
                                        let ((e1x, t1):c1, (e2x, t2):c2) = (getConstraints e1, getConstraints e2) in
                                            [(TVar bx, TInt), (t1, TInt), (t2, TInt), (e1x, t1), (e2x, t2)] ++ c1 ++ c2
getConstraints (Binary (Mul) e1 e2) = let bx = getNewVar 7 in
                                        let ((e1x, t1):c1, (e2x, t2):c2) = (getConstraints e1, getConstraints e2) in
                                            [(TVar bx, TInt), (t1, TInt), (t2, TInt), (e1x, t1), (e2x, t2)] ++ c1 ++ c2
getConstraints (Binary (Div) e1 e2) = let bx = getNewVar 8 in
                                        let ((e1x, t1):c1, (e2x, t2):c2) = (getConstraints e1, getConstraints e2) in
                                            [(TVar bx, TInt), (t1, TInt), (t2, TInt), (e1x, t1), (e2x, t2)] ++ c1 ++ c2
getConstraints (Binary (And) e1 e2) = let bx = getNewVar 9 in
                                        let ((e1x, t1):c1, (e2x, t2):c2) = (getConstraints e1, getConstraints e2) in
                                            [(TVar bx, TBool), (t1, TBool), (t2, TBool), (e1x, t1), (e2x, t2)] ++ c1 ++ c2
getConstraints (Binary (Or) e1 e2) = let bx = getNewVar 10 in
                                        let ((e1x, t1):c1, (e2x, t2):c2) = (getConstraints e1, getConstraints e2) in
                                            [(TVar bx, TBool), (t1, TBool), (t2, TBool), (e1x, t1), (e2x, t2)] ++ c1 ++ c2
getConstraints (If b t f) = let ix = getNewVar 20 in
                                let ((bx, bt):c1, (tx, tt):c2, (fx, ft):c3) = (getConstraints b, getConstraints t, getConstraints f) in
                                    [(TVar ix, tt), (tt, ft), (bt, TBool), (bx, bt), (tx, tt), (fx, ft)] ++ c1 ++ c2 ++ c3
getConstraints (Declare x e body) = (getConstraints (substExp x e body)) ++ getConstraints(e)
getConstraints (Variable x) = error ("Unbounded variable " ++ x)
getConstraints (Function x e) = let (funx, fromx, tox) = (getNewVar 31, getNewVar 32, getNewVar 33) in
                                    [(TVar funx, TFun (TVar fromx) (TVar tox))]
getConstraints (Call (Function x e) arg) = let cx = getNewVar 30 in
                                            let ((argx, argt):c1, (funx, funt):c2, (ex, et):c3) = (getConstraints arg, getConstraints (Function x e), getConstraints (substExp x arg e)) in
                                                case funt of
                                                    (TFun fromt tot) -> [(TVar cx, tot), (tot, et), (fromt, argt), (argx,argt), (funx, funt), (ex,et)] ++ c1 ++ c2 ++ c3
                                                    _ -> error "Function type doesn't look like function"
getConstraints (Call _ arg) = error "Cannot call non-function"

getConstraints _ = []

unify :: [(Type, Type)] -> [(String, Type)]
unify [] = []
unify ((s,t):c') = if s==t
                    then unify(c')
                    else unifyA ((s,t):c')

unifyA :: [(Type, Type)] -> [(String, Type)]
unifyA ((TVar svar, t):c') = if svar `notElem` (freevars t)
                                then (svar,t):(unify(substAll svar t c'))
                                else unifyB ((TVar svar,t):c')
unifyA z = unifyB z

unifyB :: [(Type, Type)] -> [(String, Type)]
unifyB ((s, TVar tvar):c') = if tvar `notElem` (freevars s)
                                then (tvar,s):(unify(substAll tvar s c'))
                                else unifyC ((s,TVar tvar):c')
unifyB z = unifyC z

unifyC :: [(Type, Type)] -> [(String, Type)]
unifyC ((TFun s1 s2, TFun t1 t2):c') = unify ([(s1,t1),(s2,t2)] ++ c')
unifyC _ = error "Cannot unify!"

freevars :: Type -> [String]
freevars (TVar s) = [s]
freevars (TFun t1 t2) = freevars(t1) ++ freevars(t2)
freevars (TPoly ss t) = ss ++ freevars(t)
freevars _ = []

substAll :: String -> Type -> [(Type,Type)] -> [(Type,Type)]
substAll s t c = [(subst s t t1, subst s t t2) | (t1,t2) <- c]

subst :: String -> Type -> Type -> Type
subst s t (TVar s1) = if s == s1
                            then t
                            else (TVar s1)
subst s t (TFun t1 t2) = TFun (subst s t t1) (subst s t t2)
subst s t (TPoly ss t') = if s `elem` ss
                            then TPoly ss t'
                            else TPoly ss (subst s t t')
subst _ _ t = t

substExp :: String -> Exp -> Exp -> Exp
substExp _ _ (Literal v) = Literal v
substExp x e (Unary uop e1) = Unary uop (substExp x e e1)
substExp x e (Binary bop e1 e2) = Binary bop (substExp x e e1) (substExp x e e2)
substExp x e (If b t f) = If (substExp x e b) (substExp x e t) (substExp x e f)
substExp x e (Variable y) = if x == y
                                then e
                                else (Variable y)
substExp x e (Declare y e' b) = if x == y
                                    then (Declare y (substExp x e e') b)
                                    else (Declare y (substExp x e e') (substExp x e b))
substExp x e (Function y e') = if x == y
                                    then (Function y e')
                                    else (Function y (substExp x e e'))
substExp x e (Call e1 e2) = Call (substExp x e e1) (substExp x e e2)

-- Code to display expressions
instance Show Exp where
  show e = "[" ++ showExp 0 e ++ "]"

showExp level (Literal i)      = show i
showExp level (Variable x)    = x
showExp level (Declare x a b) = 
  if level > 0 then paren result else result
    where result = "let " ++ x ++ " = " ++ showExp 0 a ++ " in " ++ showExp 0 b
showExp level (If a b c)    = 
  if level > 0 then paren result else result
    where result = "if (" ++ showExp 0 a ++ ") " ++ showExp 0 b ++ "; else " ++ showExp 0 c
showExp level (Unary Neg a)    = "-" ++ showExp 99 a
showExp level (Unary Not a)    = "!" ++ showExp 99 a
showExp level (Binary op a b)  = showBinary level (fromJust (lookup op levels)) a (fromJust (lookup op names)) b
  where levels = [(Or, 1), (And, 2), (GT, 3), (LT, 3), (LE, 3), (GE, 3), (EQ, 3), 
                  (Add, 4), (Sub, 4), (Mul, 5), (Div, 5)] 
        names = [(Or, "||"), (And, "&&"), (GT, ">"), (LT, "<"), (LE, "<="), (GE, ">="), (EQ, "=="), 
                  (Add, "+"), (Sub, "-"), (Mul, "*"), (Div, "/")] 
showExp level (Function x body)    = "fun(" ++ x ++ ") " ++ showExp 0 body
showExp level (Call fun arg)    = 
	paren (showExp 6 fun ++ " " ++ showExp 6 arg)

showBinary outer inner a op b =
  if inner < outer then paren result else result
      where result = showExp inner a ++ " " ++ op ++ " " ++ showExp inner b
      
paren x = "(" ++ x ++ ")"

data Type = TInt
          | TBool
          | TVar String
          | TFun Type Type
          | TPoly [String] Type
          | TError
  deriving Eq
instance Show Type where
  show TInt = "Int"
  show TBool = "Bool"
  show (TVar s) = s
  show (TFun t1 t2) = "("++show t1++" -> "++show t2++")"
  show (TPoly fv typ) = "forall"++show fv++".("++show typ++")"
  show TError = "Type error!"

