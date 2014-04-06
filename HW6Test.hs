module HW6Test where

import HW6
import HW6Parse

e1 = "2 + 23 * (3 + 2) / 2"
e2 = "let x = 3 in x * x" 
e3 = "let f = fun(x) x in f(3)"
e4 = "let T = fun(x) fun(y) x in let F = fun(x) fun(y) y in T F"
e5 = "let y = 2 in let f = fun(n) n * y in f y + 3"

main = do
  print e1
  print (infer (parseExp e1))
  print e2
  print (infer (parseExp e2))
  print e3
  print (infer (parseExp e3))
  print e4
  print (infer (parseExp e4))
  print e5
  print (infer (parseExp e5))
