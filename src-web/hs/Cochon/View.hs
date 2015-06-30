{-# LANGUAGE PatternSynonyms, OverloadedStrings, TypeFamilies,
  MultiParamTypeClasses, LambdaCase, LiberalTypeSynonyms, DataKinds,
  NamedFieldPuns, TypeOperators, RebindableSyntax, TypeSynonymInstances,
  FlexibleInstances #-}

module Cochon.View where

import Prelude hiding ((>>), return)

import Control.Applicative
import qualified Data.Foldable as Foldable
import Data.Monoid
import Data.List
import Data.String
import Data.Text (Text)
import Data.Traversable as Traversable
import Data.Void

import Lens.Family2
import React
import React.DOM hiding (label_)
import React.GHCJS
import React.MaterialUI

import Cochon.CommandLexer
import Cochon.Controller
import Cochon.TermController
import Cochon.Error
import Cochon.Model
import Cochon.Tactics
import Cochon.Reactify
import DisplayLang.Lexer
import DisplayLang.Name
import DisplayLang.TmParse
import DisplayLang.DisplayTm
import DisplayLang.PrettyPrint
import DisplayLang.Scheme
import Distillation.Distiller
import Distillation.Scheme
import Elaboration.Elaborator
import Elaboration.Scheduler
import Elaboration.ElabProb
import Elaboration.ElabMonad
import Elaboration.MakeElab
import Elaboration.RunElab
import Evidences.DefinitionalEquality
import Evidences.Eval hiding (($$))
import qualified Evidences.Eval (($$))
import Evidences.Tm
import Kit.BwdFwd
import Kit.ListZip
import Kit.Parsley
import NameSupply.NameSupply
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
import ProofState.Structure.Developments
import ProofState.Structure.Entries

import Tactics.Data
import Tactics.Elimination
import Tactics.IData
import Tactics.Matching
import Tactics.ProblemSimplify
import Tactics.PropositionSimplify
import Tactics.Record
import Tactics.Relabel
import Tactics.Unification

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


page_ :: InteractionState
      -> [AttrOrHandler Transition]
      -> ()
      -> InteractionReact
page_ state = classLeaf $ smartClass
    { React.name = "Page"
    , transition = \(state, trans) -> (dispatch trans state, Nothing)
    , initialState = state
    , renderFn = \() state -> div_ [ class_ "page" ] $ do
          div_ [ class_ "top-pane" ] $ do

              -- proofCtxDisplay $ _proofCtx state

          div_ [ class_ "bottom-pane" ] $ do
              "" -- TEMP
              -- locally $ autocompleteView (_autocomplete state)
              -- prompt state
    }
