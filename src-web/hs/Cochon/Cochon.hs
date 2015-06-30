-- Cochon Web Interface
-- ====================

{-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs,
    OverloadedStrings, NamedFieldPuns #-}

module Cochon.Cochon where

import Control.Monad.State
import qualified Data.Foldable as Foldable

import Control.Error

import DisplayLang.Lexer
import DisplayLang.Name
import DisplayLang.TmParse
import DisplayLang.DisplayTm
import DisplayLang.PrettyPrint
import DisplayLang.Scheme

import Elaboration.Error

import Evidences.Tm

import ProofState.Edition.ProofContext
import ProofState.Edition.ProofState
import ProofState.Edition.Entries
import ProofState.Edition.GetSet
import ProofState.Edition.Navigation
import ProofState.Edition.Scope

import ProofState.Interface.Search
import ProofState.Interface.ProofKit
import ProofState.Interface.Lifting
import ProofState.Interface.Module
import ProofState.Interface.NameResolution
import ProofState.Interface.Solving
import ProofState.Interface.Parameter

import Cochon.CommandLexer
import Cochon.Error
import Cochon.Model
import Cochon.View
import Cochon.Controller
import Cochon.Tactics
import Cochon.Reactify

import Kit.BwdFwd

import React.GHCJS

-- We start out here. Main calls `cochon emptyContext`.

cochon :: ProofContext -> IO ()
cochon loc = do
    Just doc <- currentDocument
    Just e <- documentGetElementById doc ("inject" :: JSString)
    let startCtx = B0 :< loc
    validateDevelopment startCtx

    let page_ = classLeaf $ smartClass
            { name = "Page"
            , renderFn = page
            , transition = dispatch
            , initialState = startState startCtx
            }

    render (page_ [] ()) e
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
