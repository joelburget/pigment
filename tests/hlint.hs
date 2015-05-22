-- Copyright: (C) 2013-2014 Edward Kmett, 2015 Joel Burget
module Main where

import Control.Monad
import Language.Haskell.HLint
import System.Environment
import System.Exit

main :: IO ()
main = do
    args <- getArgs
    hints <- hlint $ ["src-lib", "--cpp-define=HLINT", "--cpp-ansi"] ++ args
    unless (null hints) exitFailure
