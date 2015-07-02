{-# LANGUAGE RebindableSyntax, JavaScriptFFI, CPP #-}

module Cochon.View where

import Prelude hiding ((>>), return)

import qualified Data.Foldable as Foldable
import Data.String

import Lens.Family2
import React
import React.GHCJS
import React.Rebindable

import Cochon.Controller
import Cochon.Model

import Kit.BwdFwd
import NameSupply.NameSupply
import ProofState.Edition.ProofContext


import Kit.Trace


forReact :: Foldable f => f a -> (a -> ReactNode b) -> ReactNode b
forReact = flip Foldable.foldMap

-- The autocomplete overlay
type Autocomplete = ReactNode AutocompleteState

-- handlers

constTransition :: trans -> MouseEvent -> Maybe trans
constTransition = const . Just


handleEntryToggle :: Name -> MouseEvent -> Maybe TermAction
handleEntryToggle = constTransition . ToggleTerm


handleEntryGoTo :: Name -> MouseEvent -> Maybe TermAction
handleEntryGoTo = constTransition . GoToTerm


handleToggleAnnotate :: Name -> MouseEvent -> Maybe TermAction
handleToggleAnnotate = constTransition . ToggleAnnotate


-- TODO(joel) - stop faking this
handleAddConstructor :: Name -> MouseEvent -> Maybe TermAction
handleAddConstructor _ _ = Nothing

handleToggleEntry :: Name -> MouseEvent -> Maybe Transition
-- handleToggleEntry name _ = Just $ ToggleEntry name
handleToggleEntry = constTransition . ToggleEntry

-- TODO(joel) this and handleEntryClick duplicate functionality
handleGoTo :: Name -> MouseEvent -> Maybe Transition
handleGoTo = constTransition . GoTo

handleKey :: KeyboardEvent -> Maybe Transition
handleKey KeyboardEvent{React.key="Enter"}     = Just $ CommandKeypress Enter
handleKey KeyboardEvent{React.key="Tab"}       = Just $ CommandKeypress Tab
handleKey KeyboardEvent{React.key="ArrowUp"}   = Just $ CommandKeypress UpArrow
handleKey KeyboardEvent{React.key="ArrowDown"} = Just $ CommandKeypress DownArrow
handleKey _ = Nothing

handleCmdChange :: ChangeEvent -> Maybe Transition
handleCmdChange = Just . CommandTyping . fromJSString . value . target


-- views


page_ :: InteractionState -> ReactNode a
page_ initialState =
    let cls = smartClass
          { React.name = "Page"
          , transition = \(state, trans) -> (dispatch trans state, Nothing)
          , initialState = initialState
          , renderFn = \() state -> pageLayout_ $ do
                editView_ (state^.proofCtx)
                commandLine_ (state^.autocomplete)
          }
    in classLeaf cls ()

foreign import javascript "window.PigmentView.PageLayout" pageLayout
    :: ImportedClass Transition

pageLayout_ :: ReactNode Transition -> ReactNode Transition
pageLayout_ = importParentClass pageLayout

-- Top-level views:
-- * develop / debug / chiusano edit
-- * node history (better: node focus?)
-- * edit

editView_ :: Bwd ProofContext -> ReactNode Transition
editView_ = classLeaf $ smartClass
    { React.name = "Edit View"
    , transition = \(state, trans) -> (state, trans)
    , renderFn = \_ _ -> "Edit View"
    }

commandLine_ :: AutocompleteState -> ReactNode Transition
commandLine_ = classLeaf $ smartClass
    { React.name = "Command Line"
    , transition = \(state, trans) -> (state, trans)
    , renderFn = \_ _ -> "Command Line"
    }
