{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
module Cochon.TermController where

import Control.Arrow
import qualified Data.Text as T

import Kit.BwdFwd
import Cochon.Model
import Cochon.Tactics
import DisplayLang.Name
import NameSupply.NameSupply
import ProofState.Edition.ProofContext
import ProofState.Edition.ProofState
import ProofState.Interface.Search

import Evidences.Tm

-- util

execProofState :: forall a. ProofState a
               -> ProofContext
               -> Either UserMessage ProofContext
execProofState state = left (stackMessage Red "stack!") . right snd . runProofState state


toggleAnnotate :: Name -> InteractionState -> InteractionState
toggleAnnotate name state@InteractionState{_proofCtx=ctxs :< ctx} =
    case execProofState (toggleEntryAnnotate name) ctx of
        Left err -> state
        Right ctx' -> state{_proofCtx=ctxs :< ctx'}


termDispatch :: TermTransition -> InteractionState -> InteractionState
termDispatch (ToggleTerm name) state = state
termDispatch (GoToTerm name) state = state
termDispatch (BeginDrag name) state = state
termDispatch (ToggleAnnotate name) state = toggleAnnotate name state
-- termDispatch (AnnotationTyping name text) state = state
