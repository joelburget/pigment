{-# LANGUAGE TypeOperators, GADTs, KindSignatures,
    TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables,
    OverloadedStrings #-}

module Pig where

import Control.Applicative
import Control.Monad.State
import Data.Foldable as Foldable
import Data.List
import Data.String
import System.Environment
import System.IO
import System.Console.GetOpt

import Kit.BwdFwd
import Kit.Parsley

import Cochon.Controller
import Cochon.DevLoad
import Cochon.Model
import Cochon.Tactics
import DisplayLang.Lexer
import DisplayLang.Name
import DisplayLang.PrettyPrint
import Distillation.Distiller
import Elaboration.Error
import Evidences.Tm
import ProofState.Edition.GetSet
import ProofState.Edition.ProofContext
import ProofState.Edition.ProofState
import ProofState.Interface.NameResolution
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

-- cochon' :: Bwd ProofContext -> IO ()
-- cochon' (locs :< loc) = do
--     -- Safety belt: this *must* type-check!
--     validateDevelopment (locs :< loc)
--     -- Show goal and prompt
--     case runProofState showPrompt loc of
--         Left err -> print err
--         Right (str, _) -> do
--             putStr str
--             hFlush stdout
--     l <- getLine
--     case parse tokenize l of
--         Left pf -> do
--             putStrLn ("Tokenize failure: " ++ describePFailure pf id)
--             cochon' (locs :< loc)
--         Right ts ->
--           case parse pCochonTactics ts of
--               Left pf -> do
--                   putStrLn ("Parse failure: " ++ describePFailure pf (intercalate " " . map crushToken))
--                   cochon' (locs :< loc)
--               Right cds -> do
--                   locs' <- doCTactics cds (locs :< loc)
--                   cochon' locs'

-- showPrompt :: ProofState String
-- showPrompt = do
--     mty <- optional getHoleGoal
--     case mty of
--         Just (_ :=>: ty)  -> (++) <$> showGoal ty <*> showInputLine
--         Nothing           -> showInputLine
--   where
--     showGoal :: TY -> ProofState String
--     showGoal ty@(LABEL _ _) = do
--         -- h <- infoHypotheses
--         s <- prettyHere . (SET :>:) =<< bquoteHere ty
--         return $ {- h ++ "\n" ++ -} "Programming: " ++ show s ++ "\n"
--     showGoal ty = do
--         s <- prettyHere . (SET :>:) =<< bquoteHere ty
--         return $ "Goal: " ++ show s ++ "\n"

--     showInputLine :: ProofState String
--     showInputLine = do
--         mn <- optional getCurrentName
--         case mn of
--             Just n   -> return $ showName n ++ " > "
--             Nothing  -> return "> "

tacs :: [CochonTactic]
tacs = showTac : cochonTactics

showTac :: CochonTactic
showTac = unaryStringCT "show" (\s -> case s of
        -- "inscope"  -> infoInScope
        "context"  -> (fromString . show) <$> infoContext
        "dump"     -> fromString <$> infoDump
        "hyps"     -> (fromString . show) <$> infoHypotheses
        "state"    -> fromString <$> prettyProofState
        _          -> return "show: please specify exactly what to show."
      )
      "show <inscope/context/dump/hyps/state> - displays useless information."

-- infoInScope :: ProofState UserMessage
-- infoInScope = do
--     pc <- get
--     inScope <- getInScope
--     return (showEntries (inBScope pc) inScope)

infoDump :: ProofState String
infoDump = gets show

pCochonTactics :: Parsley Token [CTData]
pCochonTactics = pSepTerminate (keyword KwSemi) (pTactic tacs)

main :: IO ()
main = do
       argv <- getArgs
       case getOpt RequireOrder options argv of
         -- Help:
         (Help : _, _, [])            -> do
           putStrLn $ usageInfo message options
         -- -- Load a development:
         -- (LoadFile file : _, _, [])   -> do
         --   loadDev file
         -- Check a development:
         (CheckFile file : _, _, [])  -> do
           withFile file (\loc -> do
                                  validateDevelopment loc
                                  putStrLn "Loaded.")
         -- Print a development:
         (PrintFile file : _, _, [])  -> do
           withFile file printTopDev
         -- -- Load a development (no flag provided):
         -- ([],(file:[]),[])            -> do
         --   loadDev file
         -- Error:
         (_,_,errs)                   -> do
           ioError (userError (Prelude.concat errs ++
                               usageInfo message options))
 where
   withFile :: String -> (Bwd ProofContext -> IO a) -> IO a
   withFile "-" g = devLoad' tacs stdin (return []) >>= g
   withFile file g = devLoad tacs file >>= g

   -- loadDev :: String -> IO ()
   -- loadDev file = withFile file cochon'

   printTopDev :: Bwd ProofContext -> IO ()
   printTopDev (_ :< loc) = do
       let Right s = evalStateT prettyProofState loc
       putStrLn s
