{-# LANGUAGE ForeignFunctionInterface, JavaScriptFFI, CPP, OverloadedStrings #-}

module Cochon.Imports where

import qualified Data.Aeson as Aeson
import Data.HashMap.Strict as H
import Data.Monoid
import Data.String
import Data.Text (Text)
import qualified Data.Vector as V
import Data.Void
import React
import React.GHCJS
import React.Rebindable

import Cochon.Model



makeTag :: Text -> Aeson.Value
makeTag text = Aeson.Object $ H.singleton "tag" (Aeson.String text)


pageLayout_ :: ReactNode Transition -> ReactNode Transition

parameterLayout_ :: ReactNode TermTransition -> ReactNode TermTransition

definitionLayout_ :: ReactNode TermTransition -> ReactNode TermTransition

entryModuleLayout_ :: ReactNode TermTransition -> ReactNode TermTransition

devLayout_ :: ReactNode TermTransition -> ReactNode TermTransition

entriesLayout_ :: ReactNode TermTransition -> ReactNode TermTransition

entryHeaderLayout_ :: ReactNode TermTransition -> ReactNode TermTransition

moduleHeaderLayout_ :: ReactNode TermTransition -> ReactNode TermTransition

entryEntityLayout_ :: ReactNode TermTransition -> ReactNode TermTransition

messagesLayout_ :: ReactNode Transition -> ReactNode Transition

nameLayout_ :: ReactNode Void -> ReactNode Void

namePieceLayout_ :: Text -> Text -> ReactNode Void

messageLayout_ :: ReactNode Void -> ReactNode Void

messagePartLayout_ :: Text -> Text -> ReactNode Void



sigmaLayout_ :: Text -> ReactNode TermTransition -> ReactNode TermTransition

schemeLayout_ :: Text -> ReactNode TermTransition -> ReactNode TermTransition

pairLayout_ :: ReactNode TermTransition -> ReactNode TermTransition

dheadLayout_ :: Text -> ReactNode TermTransition -> ReactNode TermTransition

canLayout_ :: Text -> ReactNode TermTransition -> ReactNode TermTransition

piLayout_ :: ReactNode TermTransition -> ReactNode TermTransition

dscopeLayout_ :: ReactNode TermTransition -> ReactNode TermTransition

dInTmRNLayout_ :: Text -> ReactNode TermTransition -> ReactNode TermTransition

dExTmRNLayout_ :: ReactNode TermTransition -> ReactNode TermTransition

dspineLayout_ :: ReactNode TermTransition -> ReactNode TermTransition

relnameLayout_ :: ReactNode TermTransition -> ReactNode TermTransition

relnamePieceLayout_ :: Text -> Text -> Text -> ReactNode TermTransition

dependentParamLayout_ :: Text
                      -> ReactNode TermTransition
                      -> ReactNode TermTransition

justPiLayout_ :: ReactNode TermTransition
              -> ReactNode TermTransition
              -> ReactNode TermTransition


tacticLayout_ :: Text -> ReactNode Void -> ReactNode Void

paramLayout_ :: Text -> ReactNode Void -> ReactNode Void

tacticFormatLayout_ :: Text -> ReactNode Void -> ReactNode Void

autocompleteWelcome_ :: ReactNode Void


#ifdef __GHCJS__


foreign import javascript "window.PigmentView.PageLayout"
    pageLayout :: ImportedClass NoProps Transition

pageLayout_ = importParentClass pageLayout noProps


foreign import javascript "window.PigmentView.ParameterLayout"
    parameterLayout :: ImportedClass NoProps TermTransition

parameterLayout_ = importParentClass parameterLayout noProps


foreign import javascript "window.PigmentView.DefinitionLayout"
    definitionLayout :: ImportedClass NoProps TermTransition

definitionLayout_ = importParentClass definitionLayout noProps


foreign import javascript "window.PigmentView.EntryModuleLayout"
    entryModuleLayout :: ImportedClass NoProps TermTransition

entryModuleLayout_ = importParentClass entryModuleLayout noProps


foreign import javascript "window.PigmentView.DevLayout"
    devLayout :: ImportedClass NoProps TermTransition

devLayout_ = importParentClass devLayout noProps


foreign import javascript "window.PigmentView.EntriesLayout"
    entriesLayout :: ImportedClass NoProps TermTransition

entriesLayout_ = importParentClass entriesLayout noProps


foreign import javascript "window.PigmentView.EntryHeaderLayout"
    entryHeaderLayout :: ImportedClass NoProps TermTransition

entryHeaderLayout_ = importParentClass entryHeaderLayout noProps


foreign import javascript "window.PigmentView.ModuleHeaderLayout"
    moduleHeaderLayout :: ImportedClass NoProps TermTransition

moduleHeaderLayout_ = importParentClass moduleHeaderLayout noProps


foreign import javascript "window.PigmentView.EntryEntityLayout"
    entryEntityLayout :: ImportedClass NoProps TermTransition

entryEntityLayout_ = importParentClass entryEntityLayout noProps


foreign import javascript "window.PigmentView.RefLayout"
    refLayout :: ImportedClass NoProps TermTransition

refLayout_ = importParentClass refLayout noProps


foreign import javascript "window.PigmentView.NameLayout"
    nameLayout :: ImportedClass NoProps Void

nameLayout_ = importParentClass nameLayout noProps


foreign import javascript "window.PigmentView.NamePieceLayout"
    namePieceLayout :: ImportedClass Aeson.Value Void

namePieceLayout_ str n =
    let props = Aeson.Object $ H.fromList
            [ ("str", Aeson.String str)
            , ("n", Aeson.String n)
            ]
    in importLeafClass namePieceLayout props


foreign import javascript "window.PigmentView.MessagesLayout"
    messagesLayout :: ImportedClass NoProps Transition

messagesLayout_ = importParentClass messagesLayout noProps


foreign import javascript "window.PigmentView.MessageLayout"
    messageLayout :: ImportedClass NoProps Void

messageLayout_ = importParentClass messageLayout noProps


foreign import javascript "window.PigmentView.MessagePartLayout"
    messagePartLayout :: ImportedClass Aeson.Value Void

messagePartLayout_ text severity =
    let props = Aeson.Object $ H.fromList
            [ ("text", Aeson.String text)
            , ("severity", Aeson.String severity)
            ]
    in importLeafClass messagePartLayout props


foreign import javascript "window.PigmentView.SigmaLayout"
    sigmaLayout :: ImportedClass Aeson.Value TermTransition

sigmaLayout_ text = importParentClass sigmaLayout (makeTag text)


foreign import javascript "window.PigmentView.SchemeLayout"
    schemeLayout :: ImportedClass Aeson.Value TermTransition

schemeLayout_ text = importParentClass schemeLayout (makeTag text)


foreign import javascript "window.PigmentView.PairLayout"
    pairLayout :: ImportedClass NoProps TermTransition

pairLayout_ = importParentClass pairLayout noProps


foreign import javascript "window.PigmentView.DHeadLayout"
    dheadLayout :: ImportedClass Aeson.Value TermTransition

dheadLayout_ text = importParentClass dheadLayout (makeTag text)


foreign import javascript "window.PigmentView.CanLayout"
    canLayout :: ImportedClass Aeson.Value TermTransition

canLayout_ text = importParentClass canLayout (makeTag text)


foreign import javascript "window.PigmentView.PiLayout"
    piLayout :: ImportedClass NoProps TermTransition

piLayout_ = importParentClass piLayout noProps


foreign import javascript "window.PigmentView.DScopeLayout"
    dscopeLayout :: ImportedClass NoProps TermTransition

dscopeLayout_ = importParentClass dscopeLayout noProps


foreign import javascript "window.PigmentView.DInTmRNLayout"
    dInTmRNLayout :: ImportedClass Aeson.Value TermTransition

dInTmRNLayout_ text = importParentClass dInTmRNLayout (makeTag text)


foreign import javascript "window.PigmentView.DExTmRNLayout"
    dExTmRNLayout :: ImportedClass NoProps TermTransition

dExTmRNLayout_ = importParentClass dExTmRNLayout noProps


foreign import javascript "window.PigmentView.DSpineLayout"
    dspineLayout :: ImportedClass NoProps TermTransition

dspineLayout_ = importParentClass dspineLayout noProps


foreign import javascript "window.PigmentView.RelNameLayout"
    relnameLayout :: ImportedClass NoProps TermTransition

relnameLayout_ = importParentClass relnameLayout noProps


foreign import javascript "window.PigmentView.RelNamePieceLayout"
    relnamePieceLayout :: ImportedClass Aeson.Value TermTransition

relnamePieceLayout_ tag n str =
    let props = Aeson.Object $ H.fromList
            [ ("tag", Aeson.String tag)
            , ("n", Aeson.String n)
            , ("str", Aeson.String str)
            ]
    in importLeafClass relnamePieceLayout props


foreign import javascript "window.PigmentView.TacticLayout"
    tacticLayout :: ImportedClass Aeson.Value Void

tacticLayout_ text =
    let props = Aeson.Object $ H.singleton "name" (Aeson.String text)
    in importParentClass tacticLayout props


foreign import javascript "window.PigmentView.ParamLayout"
    paramLayout :: ImportedClass Aeson.Value Void

paramLayout_ text =
    let props = Aeson.Object $ H.singleton "name" (Aeson.String text)
    in importParentClass paramLayout props


foreign import javascript "window.PigmentView.TacticFormatLayout"
    tacticFormatLayout :: ImportedClass Aeson.Value Void

tacticFormatLayout_ tag =
    importParentClass tacticFormatLayout (makeTag tag)


foreign import javascript "window.PigmentView.AutocompleteWelcome"
    autocompleteWelcome :: ImportedClass NoProps Void

autocompleteWelcome_ = importLeafClass autocompleteWelcome noProps


foreign import javascript "window.PigmentView.DependentParamLayout"
    dependentParamLayout :: ImportedClass Aeson.Value TermTransition

dependentParamLayout_ name =
    let props = Aeson.Object $ H.singleton "name" (Aeson.String name)
    in importParentClass dependentParamLayout props


foreign import javascript "window.PigmentView.JustPiLayout"
    justPiLayout :: ImportedClass NoProps TermTransition


justPiLayout_ s t = importParentClass justPiLayout noProps (s <> t)


#else


pageLayout_ = error "pageLayout_ not available from ghc"

parameterLayout_ = error "parameterLayout_ not available from ghc"

definitionLayout_ = error "definitionLayout_ not available from ghc"

entryModuleLayout_ = error "entryModuleLayout_ not available from ghc"

devLayout_ = error "devLayout_ not available from ghc"

entriesLayout_ = error "entriesLayout_ not available from ghc"

entryHeaderLayout_ = error "entryHeaderLayout_ not available from ghc"

moduleHeaderLayout_ = error "moduleHeaderLayout_ not available from ghc"

entryEntityLayout_ = error "entryEntityLayout_ not available from ghc"

refLayout_ = error "refLayout_ not available from ghc"

nameLayout_ = error "nameLayout_ not available from ghc"

namePieceLayout_ = error "namePieceLayout_ not available from ghc"

messagesLayout_ = error "messagesLayout_ not available from ghc"

messageLayout_ = error "messageLayout_ not available from ghc"

messagePartLayout_ = error "messagePartLayout_ not available from ghc"

sigmaLayout_ = error "sigmaLayout_ not available from ghc"

schemeLayout_ = error "schemeLayout_ not available from ghc"

pairLayout_ = error "pairLayout_ not available from ghc"

dheadLayout_ = error "dheadLayout_ not available from ghc"

canLayout_ = error "canLayout_ not available from ghc"

piLayout_ = error "piLayout_ not available from ghc"

dscopeLayout_ = error "dscopeLayout_ not available from ghc"

dInTmRNLayout_ = error "dInTmRNLayout_ not available from ghc"

dExTmRNLayout_ = error "dExTmRNLayout_ not available from ghc"

dspineLayout_ = error "dspineLayout_ not available from ghc"

relnameLayout_ = error "relnameLayout_ not available from ghc"

relnamePieceLayout_ = error "relnamePieceLayout_ not available from ghc"

tacticLayout_ = error "tacticLayout_ not available from ghc"

paramLayout_ = error "paramLayout_ not available from ghc"

tacticFormatLayout_ = error "tacticFormatLayout_ not available from ghc"

autocompleteWelcome_ = error "autocompleteWelcome_ not available from ghc"

dependentParamLayout_ = error "dependentParamLayout_ not available from ghc"

justPiLayout_ = error "justPiLayout_ not available from ghc"

#endif
