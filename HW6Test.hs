module HW6Test where

import HW6
import HW6Parse

e1 = ["2 + 23 * (3 + 2) / 2"] ++
        ["let x = 3 in x * x"] ++
        ["let f = fun(x) x in f(3)"] ++
        ["let T = fun(x) fun(y) x in let F = fun(x) fun(y) y in T F"] ++
        ["let y = 2 in let f = fun(n) n * y in f y + 3"] ++
        ["2==3", "true==false", "5>6", "if true then 1 else -3", "if true then 1 else false"] ++
        ["if 1 then true else false", "if !true then !false else !false"] ++
        ["let x = true in !x", "let x = false in x+y", "let x = false in let y = 2 in if y==y then x else !x"] ++
        ["let x = x in x", "let x = x in y", "let y = 2 in let x = y in x", "fun (x) x", "fun (x) x+2"] ++
        ["fun (x) x==x", "let x = fun (x) x in x", "let x = fun (x) x in if x(true) then x(1) else x(2)"] ++
        ["let x = fun (x) x in if x(true)==x(false) then x(1)==x(2) else x(3)==x(4)"] ++
        ["let x = fun (x) x in if x(true)==x(false) then x(1)==x(2) else x(3)"] ++
        ["let x = 1 in let y = fun(x) x+y in y", "let x = 1 in let y = fun(x) x+y in x"] ++
        ["let x = fun (x) fun (x) x+x in x(true)", "let x = fun(x) fun(y) x+y in x(2)"] ++
        ["let x = fun(x) x+2 in let y = fun(x) x*4 in let z = fun(x) !x in if z(true) then x(2) else y(4)"]

evaluateAndShow e = do
    print e
    print (infer (parseExp e))
    print ""

main = do
    sequence [evaluateAndShow e | e <- e1]
