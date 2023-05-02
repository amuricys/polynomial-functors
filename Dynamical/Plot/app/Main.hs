module Main where

import OptparseHs

main :: IO ()
main = do
  opts <- parseOptions
  print opts