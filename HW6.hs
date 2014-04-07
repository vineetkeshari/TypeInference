module HW6 where

import Control.Monad.State
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
type TypeEnv = [(String, Type)]

type ConState = (Int, [(Type, Type)])
type ConValue = (Type, [(Type, Type)])

startState = (0, [])

getNewVar :: Int -> String
getNewVar nextVal = "X" ++ show(nextVal)

infer :: Exp -> Type
infer e = inferType e

inferType :: Exp -> Type
inferType e =
    let (var, cons) = evalState (getConstraints (e, [])) startState
        unified = unify (cons) in
          if anyType TError unified
            then TError
            else let typ = applySigma (unified) var
                     fvs = removeDups (freevars typ) in
                       case fvs of
                         [] -> typ
                         _ -> TPoly fvs typ

applySigma :: [(String, Type)] -> Type -> Type
applySigma [] t' = t'
applySigma ((s,t):sig) t' = applySigma sig (subst s t t')

anyType :: Type -> [(String,Type)] -> Bool
anyType _ [] = False
anyType typ ((s,t):sigma') = if t == typ
                                then True
                                else anyType typ sigma'

getConstraints :: (Exp, TypeEnv) -> State ConState ConValue
getConstraints (Literal (IntV _), typeEnv) = do
    (i, cons) <- get
    let ix = TVar (getNewVar i) in do
        put (i+1, [(ix, TInt)] ++ cons)
        (newI, newCons) <- get
        return (ix, newCons)
getConstraints (Literal (BoolV _), typeEnv) = do
    (i, cons) <- get
    let ix = TVar (getNewVar i) in do
        put (i+1, [(ix, TBool)] ++ cons)
        (newI, newCons) <- get
        return (ix, newCons)
getConstraints (Unary (Not) e, typeEnv) = do
    (ev, econs) <- getConstraints (e, typeEnv)
    (i, cons) <- get
    let ux = TVar (getNewVar i) in do
        put (i+1, [(ux, TBool), (ev, TBool)] ++ cons)
        (newCounter, newCons) <- get
        return (ux, newCons)
getConstraints (Unary (Neg) e, typeEnv) = do
    (ev, econs) <- getConstraints (e, typeEnv)
    (i, cons) <- get
    let ux = TVar (getNewVar i) in do
        put (i+1, [(ux, TInt), (ev, TInt)] ++ cons)
        (newCounter, newCons) <- get
        return (ux, newCons)
getConstraints (Binary (Add) e1 e2, typeEnv) = do
    (e1v, e1cons) <- getConstraints (e1, typeEnv)
    (e2v, e2cons) <- getConstraints (e2, typeEnv)
    (i, cons) <- get
    let bx = TVar (getNewVar i) in do
        put (i+1, [(bx, TInt), (e1v, TInt), (e2v, TInt)] ++ cons)
        (newCounter, newCons) <- get
        return (bx, newCons)
getConstraints (Binary (Sub) e1 e2, typeEnv) = do
    (e1v, e1cons) <- getConstraints (e1, typeEnv)
    (e2v, e2cons) <- getConstraints (e2, typeEnv)
    (i, cons) <- get
    let bx = TVar (getNewVar i) in do
        put (i+1, [(bx, TInt), (e1v, TInt), (e2v, TInt)] ++ cons)
        (newCounter, newCons) <- get
        return (bx, newCons)
getConstraints (Binary (Mul) e1 e2, typeEnv) = do
    (e1v, e1cons) <- getConstraints (e1, typeEnv)
    (e2v, e2cons) <- getConstraints (e2, typeEnv)
    (i, cons) <- get
    let bx = TVar (getNewVar i) in do
        put (i+1, [(bx, TInt), (e1v, TInt), (e2v, TInt)] ++ cons)
        (newCounter, newCons) <- get
        return (bx, newCons)
getConstraints (Binary (Div) e1 e2, typeEnv) = do
    (e1v, e1cons) <- getConstraints (e1, typeEnv)
    (e2v, e2cons) <- getConstraints (e2, typeEnv)
    (i, cons) <- get
    let bx = TVar (getNewVar i) in do
        put (i+1, [(bx, TInt), (e1v, TInt), (e2v, TInt)] ++ cons)
        (newCounter, newCons) <- get
        return (bx, newCons)
getConstraints (Binary (And) e1 e2, typeEnv) = do
    (e1v, e1cons) <- getConstraints (e1, typeEnv)
    (e2v, e2cons) <- getConstraints (e2, typeEnv)
    (i, cons) <- get
    let bx = TVar (getNewVar i) in do
        put (i+1, [(bx, TBool), (e1v, TBool), (e2v, TBool)] ++ cons)
        (newCounter, newCons) <- get
        return (bx, newCons)
getConstraints (Binary (Or) e1 e2, typeEnv) = do
    (e1v, e1cons) <- getConstraints (e1, typeEnv)
    (e2v, e2cons) <- getConstraints (e2, typeEnv)
    (i, cons) <- get
    let bx = TVar (getNewVar i) in do
        put (i+1, [(bx, TBool), (e1v, TBool), (e2v, TBool)] ++ cons)
        (newCounter, newCons) <- get
        return (bx, newCons)
getConstraints (Binary (GT) e1 e2, typeEnv) = do
    (e1v, e1cons) <- getConstraints (e1, typeEnv)
    (e2v, e2cons) <- getConstraints (e2, typeEnv)
    (i, cons) <- get
    let bx = TVar (getNewVar i) in do
        put (i+1, [(bx, TBool), (e1v, TInt), (e2v, TInt)] ++ cons)
        (newCounter, newCons) <- get
        return (bx, newCons)
getConstraints (Binary (LT) e1 e2, typeEnv) = do
    (e1v, e1cons) <- getConstraints (e1, typeEnv)
    (e2v, e2cons) <- getConstraints (e2, typeEnv)
    (i, cons) <- get
    let bx = TVar (getNewVar i) in do
        put (i+1, [(bx, TBool), (e1v, TInt), (e2v, TInt)] ++ cons)
        (newCounter, newCons) <- get
        return (bx, newCons)
getConstraints (Binary (GE) e1 e2, typeEnv) = do
    (e1v, e1cons) <- getConstraints (e1, typeEnv)
    (e2v, e2cons) <- getConstraints (e2, typeEnv)
    (i, cons) <- get
    let bx = TVar (getNewVar i) in do
        put (i+1, [(bx, TBool), (e1v, TInt), (e2v, TInt)] ++ cons)
        (newCounter, newCons) <- get
        return (bx, newCons)
getConstraints (Binary (LE) e1 e2, typeEnv) = do
    (e1v, e1cons) <- getConstraints (e1, typeEnv)
    (e2v, e2cons) <- getConstraints (e2, typeEnv)
    (i, cons) <- get
    let bx = TVar (getNewVar i) in do
        put (i+1, [(bx, TBool), (e1v, TInt), (e2v, TInt)] ++ cons)
        (newCounter, newCons) <- get
        return (bx, newCons)
getConstraints (Binary (EQ) e1 e2, typeEnv) = do
    (e1v, e1cons) <- getConstraints (e1, typeEnv)
    (e2v, e2cons) <- getConstraints (e2, typeEnv)
    (i, cons) <- get
    let (bx, argx) = (TVar (getNewVar i), TVar (getNewVar (i+1))) in do
        put (i+2, [(bx, TBool), (e1v, argx), (e2v, argx)] ++ cons)
        (newCounter, newCons) <- get
        return (bx, newCons)
getConstraints (If b t f, typeEnv) = do
    (bv, bcons) <- getConstraints (b, typeEnv)
    (tv, tcons) <- getConstraints (t, typeEnv)
    (fv, fcons) <- getConstraints (f, typeEnv)
    (i, cons) <- get
    let ifx = TVar (getNewVar i) in do
        put (i+1, [(ifx, tv), (tv, fv), (bv, TBool)] ++ cons)
        (newCounter, newCons) <- get
        return (ifx, newCons)
getConstraints (Function x e, typeEnv) = do
    (i0, cons0) <- get
    let argx = TVar (getNewVar i0) in do
      put (i0+1, cons0)
      (ev, econs) <- getConstraints (e, (x, argx):typeEnv)
      (i, cons) <- get
      let funx = (TVar (getNewVar i)) in do
        put (i+1, [(funx, TFun argx ev)] ++ cons)
        (newCounter, newCons) <- get
        return (funx, newCons)
getConstraints (Call fun arg, typeEnv) = do
    (argv, argcons) <- getConstraints (arg, typeEnv)
    (funv, funcons) <- getConstraints (fun, typeEnv)
    (i, cons) <- get
    let (cx, tox) = (TVar (getNewVar i), TVar (getNewVar (i+1))) in do
        put (i+2, [(cx, tox), (funv, TFun argv tox)] ++ cons)
        (newCounter, newCons) <- get
        return (cx, newCons)
getConstraints (Variable x, typeEnv) = do
    (i, cons) <- get
    let vx = TVar (getNewVar i) in do
      case lookup x typeEnv of
        Just t ->
          case t of
            TPoly fvs typ ->
              let replacedVars = [(fvs!!n, TVar (getNewVar (i+n+1))) | n <- [0..((length fvs)-1)]] in
                put (i+1+(length fvs), [(vx, applySigma replacedVars typ)] ++ cons)
            _ -> put (i+1, [(vx, t)] ++ cons)
        Nothing -> put (i+1, [(vx, TError)] ++ cons)
      (newCounter, newCons) <- get
      return (vx, newCons)
getConstraints (Declare x e body, typeEnv) = do
    (i0, cons0) <- get
    let (lenVars, fvs, applied, unified) = declareHelper e typeEnv i0 in do
      put (i0+(lenVars), cons0)
      (bv, bcons) <- getConstraints (body, (x, TPoly fvs applied):typeEnv)
      (i,cons) <- get
      let dx = TVar (getNewVar i) in do
        put (i+1, [(dx, if (anyType TError unified) then TError else bv)] ++ cons)
        (newCounter, newCons) <- get
        return (dx, newCons)
getConstraints _ = do
    (i, cons) <- get
    return (TVar "Error", cons)

declareHelper :: Exp -> TypeEnv -> Int -> (Int, [String], Type, [(String, Type)])
declareHelper e typeEnv i0 =
    let vars = [y | y <- (removeDups (getvars e)), lookup y typeEnv == Nothing]
        t2Env = [(vars!!n, TVar (getNewVar (i0+n))) | n <- [0..((length vars)-1)]] ++ typeEnv
        (t2v, t2cons) = evalState (getConstraints (e, t2Env)) startState
        unified = unify t2cons
        applied = applySigma unified t2v
        fvs = removeDups (freevars applied) in
          (length vars, fvs, applied, unified)
      
getvars :: Exp -> [String]
getvars (Literal _) = []
getvars (Unary _ e) = getvars e
getvars (Binary _ e1 e2) = (getvars e1) ++ (getvars e2)
getvars (If b t f) = (getvars b) ++ (getvars t) ++ (getvars f)
getvars (Function x e) = [y | y <- (getvars e), y /= x]
getvars (Call e1 e2) = (getvars e1) ++ (getvars e2)
getvars (Declare x e b) = (getvars e) ++ [y | y <- (getvars b), y /= x]
getvars (Variable v) = [v]

unify :: [(Type, Type)] -> [(String, Type)]
unify [] = []
unify ((s,t):c') = 
    if s == TError || t == TError
        then [("ERROR", TError)]
        else if s==t
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
unifyC _ = [("ERROR", TError)]

freevars :: Type -> [String]
freevars (TVar s) = [s]
freevars (TFun t1 t2) = freevars(t1) ++ freevars(t2)
freevars (TPoly ss t) = ss ++ freevars(t)
freevars _ = []

removeDups :: [String] -> [String]
removeDups s = unique [] s

unique :: [String] -> [String] -> [String]
unique seen [] = []
unique seen (x:xs) = if x `notElem` seen
                    then (x:(unique (x:seen) xs))
                    else (unique seen xs)

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

