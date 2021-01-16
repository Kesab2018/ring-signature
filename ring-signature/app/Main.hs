module Main where
import Control.Monad

import Lib

main :: IO ()
main = do
  l <- replicateM 100 test
  let t = all (== True) l
  print t