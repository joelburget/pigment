{-# LANGUAGE RebindableSyntax, OverloadedStrings, CPP, TypeOperators #-}

module Cochon.View where

import Prelude hiding ((>>), return)

import qualified Data.Foldable as Foldable
import Data.Monoid
import Data.String
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void

import Lens.Family2
import React hiding (key)
import qualified React
import React.DOM
import React.GHCJS
import React.Rebindable

import Cochon.Controller
import Cochon.Imports
import Cochon.Model
import Cochon.Reactify

import Distillation.Distiller
import Distillation.Scheme
import Evidences.Tm
import Kit.BwdFwd
import Kit.ListZip
import NameSupply.NameSupply
import ProofState.Edition.ProofContext
import ProofState.Structure.Developments


-- handlers

constTransition :: trans -> MouseEvent -> Maybe trans
constTransition = const . Just


handleEntryToggle :: Name -> MouseEvent -> Maybe TermTransition
handleEntryToggle = constTransition . ToggleTerm


handleEntryGoTo :: Name -> MouseEvent -> Maybe TermTransition
handleEntryGoTo = constTransition . GoToTerm


handleToggleAnnotate :: Name -> MouseEvent -> Maybe TermTransition
handleToggleAnnotate = constTransition . ToggleAnnotate


-- TODO(joel) - stop faking this
handleAddConstructor :: Name -> MouseEvent -> Maybe TermTransition
handleAddConstructor _ _ = Nothing

-- handleToggleEntry :: Name -> MouseEvent -> Maybe Transition
-- handleToggleEntry name _ = Just $ ToggleEntry name
-- handleToggleEntry = constTransition . ToggleEntry

-- TODO(joel) this and handleEntryClick duplicate functionality
-- handleGoTo :: Name -> MouseEvent -> Maybe Transition
-- handleGoTo = constTransition . GoTo


-- views


page_ :: InteractionState -> ReactNode a
page_ initialState =
    let cls = smartClass
          { React.name = "Page"
          , transition = \(state, trans) -> (dispatch trans state, Nothing)
          , initialState = initialState
          , renderFn = \() state -> pageLayout_ $ do
                editView_ (state^.proofCtx)
                messages_ (state^.messages)

                -- testing only
                -- locally $ paramLayout_
                --     (ctName dataTac)
                --     (do text_ (ctMessage dataTac)
                --         tacticFormat_ (ctDesc dataTac)
                --     )
          }
    in classLeaf cls ()

messages_ :: [UserMessage] -> ReactNode Transition
messages_ = classLeaf $ smartClass
    { React.name = "Messages"
    , transition = \(state, trans) -> (state, Just trans)
    , renderFn = \msgs _ -> messagesLayout_ $
        forReact msgs message_
    }


message_ :: UserMessage -> ReactNode Transition
message_ = classLeaf $ smartClass
    { React.name = "Message"
    , transition = \(state, trans) -> (state, Just trans)
    , renderFn = \(UserMessage parts) _ -> locally $ messageLayout_ $
        forReact parts messagePart_
    }


messagePart_ :: UserMessagePart -> ReactNode Void
messagePart_ (UserMessagePart text maybeName stack maybeTerm severity) =
    messagePartLayout_ text (fromString (show severity))


-- Top-level views:
-- * develop / debug / chiusano edit
-- * node history (better: node focus?)
-- * edit

editView_ :: Bwd ProofContext -> ReactNode Transition
editView_ = classLeaf $ smartClass
    { React.name = "Edit View"
    , transition = \(state, trans) -> (state, Just trans)
    , renderFn = \pc _ -> case pc of
        B0 -> "Red alert - empty proof context"
        (_ :< pc@(PC _ dev _)) -> locally $ dev_ pc dev
    }

dev_ :: ProofContext -> Dev Bwd -> ReactNode TermTransition
dev_ pc (Dev entries tip nSupply suspendState) =
    devLayout_ $ do
      fromString (show suspendState)
      entriesLayout_ $ forReact entries (entry_ pc)

entry_ :: ProofContext -> Entry Bwd -> ReactNode TermTransition
entry_ pc (EEntity ref lastName entity ty meta) = entryEntityLayout_ $ do
    entryHeaderLayout_ $ do
        ref_ pc ref
        metadata_ meta
        intm_ pc (SET :>: ty)
    entity_ pc entity

entry_ pc (EModule name dev purpose meta)
    = entryModuleLayout_ $ do
        moduleHeaderLayout_ $ do
            locally $ name_ name
            purpose_ purpose
            metadata_ meta
        dev_ pc dev

intm_ :: ProofContext -> (TY :>: INTM) -> ReactNode TermTransition
intm_ pc tm =
    case runProofState (distillHere tm) pc of
        Left err -> "ERR: runProofState"
        Right (inTmRn :=>: _, _) -> dInTmRN_ inTmRn

ref_ :: ProofContext -> REF -> ReactNode TermTransition
ref_ pc (name := rKind :<: ty) = refLayout_ $ do
    locally $ name_ name
    -- TODO rKind
    intm_ pc (SET :>: ty)

name_ :: Name -> ReactNode Void
name_ n = nameLayout_ (forReact n namePiece_)

namePiece_ :: (String, Int) -> ReactNode Void
namePiece_ (str, n) = namePieceLayout_ (T.pack str) (T.pack (show n))

purpose_ :: ModulePurpose -> ReactNode a
purpose_ p = fromString (show p)

metadata_ :: Metadata -> ReactNode a
metadata_ m = fromString (show m)

entity_ :: ProofContext -> Entity Bwd -> ReactNode TermTransition
entity_ pc (Parameter pKind) = parameterLayout_ (fromString (show pKind))
entity_ pc (Definition dKind dev) = definitionLayout_ $ do
    dev_ pc dev
    case dKind of
      LETG -> "LETG"
      PROG sch -> case runProofState (distillSchemeHere sch) pc of
          Left err -> "PROGERR"
          Right (sch', _) -> "PROG" <> scheme_ sch'
