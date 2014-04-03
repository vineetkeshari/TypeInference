module HW6test where

import HW6
import HW6parse

e = "2 + 23 * (3 + 2) / 2" :
  [ "let x = 3 in x * x" :
  [ "let f = fun(x) x in f(3)" :
  [ "let T = fun(x) fun(y) x in let F = fun(x) fun(y) y in T F" :
  [ "let y = 2 in let f = fun(n) n * y in f y + 3" ] ] ] ]

parse e = do
  [print (parseExp e1), e1 <- e]

main = do
  parse e
