{-# LANGUAGE LiberalTypeSynonyms, DeriveGeneric, TemplateHaskell,
  MultiParamTypeClasses, TypeOperators, OverloadedStrings #-}

module Cochon.Model where

import Control.Applicative
import Control.Monad.State
import Data.Monoid
import Data.String
import qualified Data.Text as T
import Data.Text (Text)
import GHC.Generics

import DisplayLang.Name
import Distillation.Distiller
import Elaboration.Error
import Evidences.Tm
import Kit.BwdFwd
import Kit.ListZip
import NameSupply.NameSupply
import ProofState.Edition.ProofContext
import ProofState.Edition.ProofState

import Lens.Family2
import Lens.Family2.TH

import React


data SpecialKey
    = Enter
    | Tab
    | UpArrow
    | DownArrow
    | Escape
    deriving Show

-- Top level transitions that the whole page can undergo
data Transition
    = TermTransition TermTransition


data TermTransition
    -- | Expand / collapse a term
    = ToggleTerm Name
    -- | Jump to a term
    | GoToTerm Name
    -- | This is kind of open ended -- where are you dragging it?
    -- I notice there's no EndDrag, yet.
    | BeginDrag Name
    -- | Names can have attached notes. Toggle its visibility.
    | ToggleAnnotate Name
    -- | AnnotationTyping Name T.Text

instance GeneralizeSignal TermTransition Transition where
    generalizeSignal = TermTransition


data MessageSeverity = Green | Orange | Red deriving Show


-- TODO UserMessage is used in Cochon.Tactics, part of src-bin. It's certainly
data UserMessagePart = UserMessagePart
    { messageText :: T.Text
    , relevantName :: Maybe Name
    , stack :: Maybe (StackError DInTmRN)
    , messageTerm :: Maybe DInTmRN
    , messageSeverity :: MessageSeverity
    } deriving Show


newtype UserMessage = UserMessage [UserMessagePart] deriving Show

instance IsString UserMessage where
    fromString str = textUserMessage Green (fromString str)

instance Monoid UserMessage where
    mempty = UserMessage []
    (UserMessage part1) `mappend` (UserMessage part2) = UserMessage (part1 `mappend` part2)


tellTermHere :: (TY :>: INTM) -> ProofState UserMessage
tellTermHere tt = do
    dtm :=>: _ <- distillHere tt
    return (termMessage Green "told term" dtm)

-- TODO replace these will defaultMessagePart

termMessage :: MessageSeverity -> T.Text -> DInTmRN -> UserMessage
termMessage severity str tm = UserMessage [UserMessagePart str Nothing Nothing (Just tm) severity]

textUserMessage :: MessageSeverity -> T.Text -> UserMessage
textUserMessage severity str = UserMessage [UserMessagePart str Nothing Nothing Nothing severity]

stackMessage :: MessageSeverity -> T.Text -> StackError DInTmRN -> UserMessage
stackMessage severity str stack = UserMessage [UserMessagePart str Nothing (Just stack) Nothing severity]

-- TODO put this in a more fitting place
-- Given a proof state command and a context, we can run the command with
-- `runProofState` to produce a message (either the response from the
-- command or the error message) and `Maybe` a new proof context.
runProofState
    :: ProofState a
    -> ProofContext
    -> Either (StackError DInTmRN) (a, ProofContext)
runProofState m loc = runStateT (m `catchStack` catchUnprettyErrors) loc


data InteractionState = InteractionState
    { _proofCtx :: Bwd ProofContext
    , _messages :: [UserMessage]
    } deriving (Generic)

$(makeLenses ''InteractionState)

startState :: Bwd ProofContext -> InteractionState
startState pc = InteractionState
    pc
    []
