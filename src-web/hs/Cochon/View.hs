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

import Cochon.CommandLexer
import Cochon.Controller
import Cochon.Imports
import Cochon.Model
import Cochon.Reactify

import DisplayLang.Lexer
import Distillation.Distiller
import Distillation.Scheme
import Evidences.Tm
import Kit.BwdFwd
import Kit.ListZip
import NameSupply.NameSupply
import ProofState.Edition.ProofContext
import ProofState.Structure.Developments


-- The autocomplete overlay
type Autocomplete = ReactNode AutocompleteState

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

handleKey :: KeyboardEvent -> Maybe CommandTransition
handleKey KeyboardEvent{React.key="Enter"}     = Just $ CommandKeypress Enter
handleKey KeyboardEvent{React.key="Tab"}       = Just $ CommandKeypress Tab
handleKey KeyboardEvent{React.key="ArrowUp"}   = Just $ CommandKeypress UpArrow
handleKey KeyboardEvent{React.key="ArrowDown"} = Just $ CommandKeypress DownArrow
-- handleKey KeyboardEvent{React.key="Escape"}    = Just $ CommandKeypress Escape
handleKey _ = Nothing

handleBlur :: BlurEvent -> Maybe CommandTransition
handleBlur _ = Just CommandBlur

handleFocus :: FocusEvent -> Maybe CommandTransition
handleFocus _ = Just CommandFocus

handleCmdChange :: ChangeEvent -> Maybe CommandTransition
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
                commandLine_ state
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
entry_ pc (EEntity ref lastName entity ty anchor meta)
    = let layout = entryEntityLayout_ $ do
            entryHeaderLayout_ $ do
                ref_ pc ref
                metadata_ meta
                intm_ pc (SET :>: ty)
            entity_ pc entity
      in case anchor of
             -- AnchScheme _ -> detailedEntityLayout entity
             -- XXX
             _ -> layout

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


-- Command Line

commandLine_ :: InteractionState -> ReactNode Transition
commandLine_ = classLeaf $ smartClass
    { React.name = "Command Line"
    , transition = \(state, trans) -> (state, Just trans)
    , renderFn = \props _ ->
          let focus = props^.commandFocus
              input = textarea_ [ autofocus_ True
                                , placeholder_ "enter a command"
                                , onChange handleCmdChange
                                , onKeyDown handleKey
                                , onBlur handleBlur
                                , onFocus handleFocus
                                ]
                                (userInput focus)
              completions = autocomplete_ (props^.autocomplete)
          in commandLineLayout_ input completions
    }


autocomplete_ :: AutocompleteState -> ReactNode TermTransition
autocomplete_ = classLeaf $ smartClass
  { React.name = "Autocomplete"
  , transition = \(state, sig) -> (state, Nothing)
  , renderFn = \auto _ -> autocompleteLayout_ $ case auto of
      CompletingTactics zipper -> locally $ tacticCompletion_ zipper
      CompletingParams tac -> locally $ paramFormat_ tac
      Welcoming -> locally $ autocompleteWelcome_
      Stowed _ -> mempty
  }


-- tactic name autocompletion / preview
tacticCompletion_ :: ListZip CochonTactic -> ReactNode Void
tacticCompletion_ = classLeaf $ smartClass
  { React.name = "Tactic Completion"
  , renderFn = \zip@(ListZip late focus early) _ ->
      let -- desc :: Foldable a => a CochonTactic -> ReactNode a
          desc tacs = forReact tacs (div_ [] . text_' . ctName)
          text_' :: T.Text -> ReactNode a
          text_' = text_ . fromString . T.unpack

          allNames = map ctName (Foldable.toList zip)

          name = ctName focus

      in tacticCompletionLayout_ allNames name $ do
             locally $ tacticPreview_ focus

             div_ [] $ desc early

             div_ [] $ text_' name
               -- div_ [] $ renderHelp $ ctHelp focus


             div_ [] $ desc late
  }


-- The preview part of tactic name autocomplete
tacticPreview_ :: CochonTactic -> ReactNode Void
tacticPreview_ (CochonTactic name message desc _ _) =
    tacticLayout_ name (text_ message <> tacticFormat_ desc)


-- parameter autocompletion
paramFormat_ :: CochonTactic -> ReactNode Void
paramFormat_ (CochonTactic name message desc _ _) =
    paramLayout_ name (text_ message <> tacticFormat_ desc)


tacticFormat_ :: TacticDescription -> ReactNode Void
tacticFormat_ = classLeaf $ dumbClass
  { React.name = "Tactic Format"
  , renderFn = \fmt _ ->
      let (tag, children) = case fmt of
              TfName name -> ("name", text_ name)
              TfKeyword k -> ("keyword", fromString (key k))
              TfInArg name Nothing -> ("inarg", text_ name)
              TfInArg name (Just explain) ->
                  ("inarg", text_ name <> text_ explain)
              TfExArg name Nothing -> ("exarg", text_ name)
              TfExArg name (Just explain) ->
                  ("exarg", text_ name <> text_ explain)
              TfScheme name Nothing -> ("scheme", text_ name)
              TfScheme name (Just explain) ->
                  ("scheme", text_ name <> text_ explain)

              TfAlternative (l, r) ->
                  ("alternative", tacticFormat_ l <> tacticFormat_ r)
              TfOption fmt -> ("option", tacticFormat_ fmt)
              TfRepeatZero fmt -> ("repeatzero", tacticFormat_ fmt)
              TfBlockSequence fmts -> ("blocksequence", forReact fmts tacticFormat_)
              TfInlineSequence fmts -> ("inlinesequence", forReact fmts tacticFormat_)
              TfBracketed bracket fmt ->
                  ("bracketed", fromString (show bracket) <> tacticFormat_ fmt)
              TfSep fmt kwd ->
                  ("sep", tacticFormat_ fmt <> fromString (key kwd))
      in tacticFormatLayout_ tag children
  }
