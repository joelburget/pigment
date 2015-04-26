module Cochon.TermController where

import Control.Arrow

import React

import Kit.BwdFwd
import Cochon.Error
import Cochon.Model
import Cochon.Tactics
import NameSupply.NameSupply
import ProofState.Edition.ProofContext
import ProofState.Edition.ProofState
import ProofState.Interface.Search


-- util

constTransition :: trans -> MouseEvent -> Maybe trans
constTransition = const . Just


execProofState :: ProofState a
               -> ProofContext
               -> Either TermReact ProofContext
execProofState state = right snd . runProofState state


handleEntryToggle :: Name -> MouseEvent -> Maybe TermAction
handleEntryToggle = constTransition . ExpandTerm


handleEntryGoTo :: Name -> MouseEvent -> Maybe TermAction
handleEntryGoTo = constTransition . GoToTerm


handleToggleAnnotate :: Name -> MouseEvent -> Maybe TermAction
handleToggleAnnotate = constTransition . ToggleAnnotate


-- TODO(joel) - stop faking this
handleAddConstructor :: Name -> MouseEvent -> Maybe TermAction
handleAddConstructor _ _ = Nothing


toggleAnnotate :: Name -> InteractionState -> InteractionState
toggleAnnotate name state@InteractionState{_proofCtx=ctxs :< ctx} =
    case execProofState (toggleEntryAnnotate name) ctx of
        Left err -> state
        Right ctx' -> state{_proofCtx=ctxs :< ctx'}


termDispatch :: TermAction -> InteractionState -> InteractionState
termDispatch (ExpandTerm name) state = state
termDispatch (GoToTerm name) state = state
termDispatch (BeginDrag name) state = state
termDispatch (ToggleAnnotate name) state = toggleAnnotate name state
termDispatch (AnnotationTyping name text) state = state
