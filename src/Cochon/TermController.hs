module Cochon.TermController where

import React

import Cochon.Model
import NameSupply.NameSupply


-- util

constTransition :: trans -> MouseEvent -> Maybe trans
constTransition = const . Just


handleEntryToggle :: Name -> MouseEvent -> Maybe TermAction
handleEntryToggle = constTransition . ExpandTerm


handleEntryGoTo :: Name -> MouseEvent -> Maybe TermAction
handleEntryGoTo = constTransition . GoToTerm


-- TODO(joel) - stop faking this
handleAddAnnotation :: Name -> MouseEvent -> Maybe TermAction
handleAddAnnotation _ _ = Nothing


-- TODO(joel) - stop faking this
handleAddConstructor :: Name -> MouseEvent -> Maybe TermAction
handleAddConstructor _ _ = Nothing


termDispatch :: TermAction -> InteractionState -> InteractionState
termDispatch (ExpandTerm name) state = state
termDispatch (GoToTerm name) state = state
termDispatch (BeginDrag name) state = state
