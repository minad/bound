module Main where

import Test.DocTest
import System.Environment

main :: IO ()
main = do
  args <- getArgs
  doctest $ args ++ ["src", "examples"]
