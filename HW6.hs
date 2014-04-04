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
  deriving (Eq,Show)
  
type Env = [(String, Value)]
type TypeEnv = [(String, Type)]

getNewVar :: String -> Int -> String
getNewVar str nextVal = str ++ show(nextVal+7)

infer :: Exp -> Type
infer e = applySigma (unify (getConstraints 1 e [] [])) (TVar "S8")

applySigma :: [(String, Type)] -> Type -> Type
applySigma [] t' = t'
applySigma ((s,t):sig) t' = applySigma sig (subst s t t')

getUnaryConstraints :: String -> Int -> Type -> Type -> Exp -> Env -> TypeEnv -> [(Type, Type)]
getUnaryConstraints var i typ1 typ2 e env typeEnv =
    let ux = getNewVar var i in
        let ((ex,t):c) = getConstraints (i*3) e env typeEnv in
            [(TVar ux, typ1), (t, typ2), (ex, t)] ++ c

getBinaryConstraints :: String -> Int -> Type -> Type -> Type -> Exp -> Exp -> Env -> TypeEnv -> [(Type, Type)]
getBinaryConstraints var i typ typ1 typ2 e1 e2 env typeEnv =
    let bx = getNewVar var i in
        let ((e1x, t1):c1, (e2x, t2):c2) = (getConstraints (i*3) e1 env typeEnv, getConstraints (i*4) e2 env typeEnv) in
            [(TVar bx, typ), (t1, typ1), (t2, typ2), (e1x, t1), (e2x, t2)] ++ c1 ++ c2

getConstraints :: Int -> Exp -> Env -> TypeEnv -> [(Type, Type)]
getConstraints i (Literal (IntV _)) env typeEnv =
    let ix = getNewVar "A" i in [(TVar ix, TInt)]
getConstraints i (Literal (BoolV _)) env typeEnv =
    let bx = getNewVar "B" i in [(TVar bx, TBool)]
getConstraints i (Unary (Not) e) env typeEnv =
    getUnaryConstraints "C" i TBool TBool e env typeEnv
getConstraints i (Unary (Neg) e) env typeEnv =
    getUnaryConstraints "D" i TInt TInt e env typeEnv
getConstraints i (Binary (Add) e1 e2) env typeEnv =
    getBinaryConstraints "E" i TInt TInt TInt e1 e2 env typeEnv
getConstraints i (Binary (Sub) e1 e2) env typeEnv =
    getBinaryConstraints "F" i TInt TInt TInt e1 e2 env typeEnv
getConstraints i (Binary (Mul) e1 e2) env typeEnv =
    getBinaryConstraints "G" i TInt TInt TInt e1 e2 env typeEnv
getConstraints i (Binary (Div) e1 e2) env typeEnv =
    getBinaryConstraints "H" i TInt TInt TInt e1 e2 env typeEnv
getConstraints i (Binary (And) e1 e2) env typeEnv =
    getBinaryConstraints "I" i TBool TBool TBool e1 e2 env typeEnv
getConstraints i (Binary (Or) e1 e2) env typeEnv =
    getBinaryConstraints "J" i TBool TBool TBool e1 e2 env typeEnv
getConstraints i (Binary (GT) e1 e2) env typeEnv =
    getBinaryConstraints "K" i TBool TInt TInt e1 e2 env typeEnv
getConstraints i (Binary (LT) e1 e2) env typeEnv =
    getBinaryConstraints "L" i TBool TInt TInt e1 e2 env typeEnv
getConstraints i (Binary (GE) e1 e2) env typeEnv =
    getBinaryConstraints "M" i TBool TInt TInt e1 e2 env typeEnv
getConstraints i (Binary (LE) e1 e2) env typeEnv =
    getBinaryConstraints "N" i TBool TInt TInt e1 e2 env typeEnv
getConstraints i (Binary (EQ) e1 e2) env typeEnv =
    let (e1x, e2x) = (getNewVar "O" i, getNewVar "P" (i+1)) in
        getBinaryConstraints "Q" i TBool (TVar e1x) (TVar e2x) e1 e2 env typeEnv
getConstraints i (If b t f) env typeEnv =
    let ix = getNewVar "R" i in
        let ((bx, bt):c1, (tx, tt):c2, (fx, ft):c3) = (getConstraints (i*3) b env typeEnv, getConstraints (i*4) t env typeEnv, getConstraints (i*5) f env typeEnv) in
            [(TVar ix, tt), (tt, ft), (bt, TBool), (bx, bt), (tx, tt), (fx, ft)] ++ c1 ++ c2 ++ c3
getConstraints i (Declare x e body) env typeEnv =
    let dx = getNewVar "S" i in
        let ((bx, bt):c1, (ex, et):c2) = (getConstraints (i*3) (substExp x e body) env typeEnv, getConstraints (i+1) e env typeEnv) in
            [(TVar dx, bt), (bx, bt), (ex, et)] ++ c1 ++ c2
getConstraints i (Variable x) env typeEnv =
    let vx = getNewVar "T" i in
        case lookup x typeEnv of
            Just t -> [(TVar vx, t)]
            Nothing -> error ("Unbound variable " ++ x)
getConstraints i (Function x e) env typeEnv =
    let (funx, argx) = (getNewVar "U" i, getNewVar "V" (i+1)) in
        let ((ex,et):c) = getConstraints (i*2) e env ((x, (TVar argx)):typeEnv) in
            [(TVar funx, TFun (TVar argx) et), (ex, et)] ++ c
getConstraints i (Call fun arg) env typeEnv =
    let cx = getNewVar "W" i in
        let ((argx, argt):c1, (funx, funt):c2) = (getConstraints (i*3) arg env typeEnv, getConstraints (i*4) fun env typeEnv) in
            case funt of
                (TFun fromt tot) -> [(TVar cx, tot), (fromt, argt), (argx, argt), (funx, funt)] ++ c1 ++ c2
                _ -> error "Function type in call doesn't look like function"
getConstraints _ _ _ _ = []

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
{-
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
-}
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

