{-# LANGUAGE TypeOperators, GADTs, KindSignatures,
    TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

module Main where

import Control.Monad.State
import Data.Foldable as Foldable
import System.Environment
import System.IO
import System.Console.GetOpt

import Kit.BwdFwd

import DisplayLang.PrettyPrint
import Elaboration.Error
import Evidences.Tm
import ProofState.Edition.ProofContext
import ProofState.Interface.ProofKit
import ProofState.Interface.Solving

import Cochon.DevLoad

data Options = LoadFile FilePath
             | CheckFile FilePath
             | PrintFile FilePath
             | Interactive
             | Help

options :: [OptDescr Options]
options = [ Option ['l'] ["load"]  (ReqArg LoadFile "FILE")   "Load the development"
          , Option ['c'] ["check"] (ReqArg CheckFile "FILE")  "Check the development"
          , Option ['p'] ["print"] (ReqArg PrintFile "FILE")  "Print the development"
          , Option ['i'] ["interactive"] (NoArg Interactive)  "Interactive mode"
          , Option ['h'] ["help"]  (NoArg Help)               "Help! Help!"
          ]

message :: String
message = "Epigram version (suc n)\n" ++
          "-----------------------\n" ++
          "Usage:\n" ++
          "\tPig [options] [input file]\n\n" ++
          "Typing 'Pig --load FILE' has the same effect as 'Pig FILE'.\n" ++
          "If no input file is given, Pig starts in the empty context.\n" ++
          "Given the file name '-', Pig will read from standard input.\n\n" ++
          "Options: "

paranoid = False
veryParanoid = False

-- XXX(joel) refactor this whole thing - remove putStrLn

validateDevelopment :: Bwd ProofContext -> IO ()
validateDevelopment locs@(_ :< loc)
    | veryParanoid = Foldable.mapM_ validateCtxt locs
    | paranoid = validateCtxt loc
    | otherwise = return ()
    where result = evalStateT
              (validateHere `catchStack` catchUnprettyErrors)
              loc
          validateCtxt loc = case result of
              Left ss -> do
                  putStrLn "*** Warning: definition failed to type-check! ***"
                  putStrLn $ renderHouseStyle $ prettyStackError ss
              _ -> return ()

main :: IO ()
main = do
       argv <- getArgs
       case getOpt RequireOrder options argv of
         -- Help:
         (Help : _, _, [])            -> do
           putStrLn $ usageInfo message options
         -- Load a development:
         (LoadFile file : _, _, [])   -> do
           loadDev file
         -- Check a development:
         (CheckFile file : _, _, [])  -> do
           withFile file (\loc -> do
                                  validateDevelopment loc
                                  putStrLn "Loaded.")
         -- Print a development:
         (PrintFile file : _, _, [])  -> do
           withFile file printTopDev
         -- Load a development (no flag provided):
         ([],(file:[]),[])            -> do
           loadDev file
         -- Error:
         (_,_,errs)                   -> do
           ioError (userError (Prelude.concat errs ++
                               usageInfo message options))
 where
   withFile :: String -> (Bwd ProofContext -> IO a) -> IO a
   withFile "-" g = devLoad' (Just stdin) (return []) >>= g
   withFile file g = devLoad file >>= g

   loadDev :: String -> IO ()
   loadDev file = withFile file cochon'

   printTopDev :: Bwd ProofContext -> IO ()
   printTopDev (_ :< loc) = do
       let Right s = evalStateT prettyProofState loc
       putStrLn s
