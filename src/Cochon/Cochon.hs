-- Cochon Web Interface
-- ====================

{-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs,
    DeriveFunctor, DeriveFoldable, DeriveTraversable, OverloadedStrings,
    CPP, NamedFieldPuns #-}

module Cochon.Cochon where

import Control.Monad.Except
import Control.Monad.State
import qualified Data.Foldable as Foldable

import DisplayLang.Lexer
import DisplayLang.Name
import DisplayLang.TmParse
import DisplayLang.DisplayTm
import DisplayLang.PrettyPrint
import DisplayLang.Reactify
import DisplayLang.Scheme

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

import Kit.BwdFwd

import Haste hiding (fromString, prompt, focus)
import Haste.JSON
import Haste.Prim
import React hiding (key)
import qualified React

-- We start out here. Main calls `cochon emptyContext`.

cochon :: ProofContext -> IO ()
cochon loc = do
    Just e <- elemById "inject"
    let startCtx = B0 :< loc
    validateDevelopment startCtx
    render e page (flip dispatch) (startState startCtx)

paranoid = False
veryParanoid = False

-- XXX(joel) refactor this whole thing - remove putStrLn - fix line
-- length - surely this can be expressed more compactly

validateDevelopment :: Bwd ProofContext -> IO ()
validateDevelopment locs@(_ :< loc) = if veryParanoid
    -- XXX: there must be a better way to do that
    then Foldable.mapM_ validateCtxt locs
    else if paranoid
        then validateCtxt loc
        else return ()
  where validateCtxt loc =
            case evalStateT (validateHere `catchError` catchUnprettyErrors) loc of
              Left ss -> do
                  putStrLn "*** Warning: definition failed to type-check! ***"
                  putStrLn $ renderHouseStyle $ prettyStackError ss
              _ -> return ()
