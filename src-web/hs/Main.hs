{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Monad.State.Lazy
import Data.Foldable as Foldable

import React
import React.GHCJS

import Cochon.Model
import Cochon.View
import DisplayLang.PrettyPrint
import Elaboration.Error
import Evidences.Tm
import Kit.BwdFwd
import ProofState.Edition.ProofContext
import ProofState.Interface.ProofKit

main :: IO ()
main = do
    Just doc <- currentDocument
    Just e <- documentGetElementById doc ("inject" :: JSString)
    let startCtx = B0 :< emptyContext
    validateDevelopment startCtx

    render (page_ (startState startCtx) [] ()) e
    return ()

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
