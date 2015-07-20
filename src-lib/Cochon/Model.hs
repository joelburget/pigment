{-# LANGUAGE LiberalTypeSynonyms, DeriveGeneric, TemplateHaskell,
  MultiParamTypeClasses, TypeOperators, OverloadedStrings #-}

module Cochon.Model where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Writer
import Data.Ord
import Data.String
import qualified Data.Text as T
import Data.Text (Text)
import GHC.Generics

import Cochon.CommandLexer
import DisplayLang.Lexer
import DisplayLang.Name
import Distillation.Distiller
import Elaboration.Error
import Evidences.Tm
import Kit.BwdFwd
import Kit.ListZip
import Kit.Parsley
import NameSupply.NameSupply
import ProofState.Edition.ProofContext
import ProofState.Edition.ProofState

import Lens.Family2
import Lens.Family2.TH

import React


-- | Some commands (state modifications) should be added to the undo stack.
--   Some should be forgotten.
data Historic
    = Historic
    | Forgotten

data SpecialKey
    = Enter
    | Tab
    | UpArrow
    | DownArrow
    | Escape
    deriving Show

-- Top level transitions that the whole page can undergo
data Transition
    = CommandTransition CommandTransition
    | TermTransition TermTransition


-- Transitions scoped to just the command line
data CommandTransition
    -- | Special keys trigger a transition to a new state
    = CommandKeypress SpecialKey
    -- | We need to track each keypress so autocomplete can do its thing
    | CommandTyping Text

    -- | Track input focus and blur
    | CommandFocus
    | CommandBlur

instance GeneralizeSignal CommandTransition Transition where
    generalizeSignal = CommandTransition


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

-- TODO(joel) - give this a TacticResult reader?
type Cmd a = WriterT UserMessage (State (Bwd ProofContext)) a

setCtx :: Bwd ProofContext -> Cmd ()
setCtx = put

getCtx :: Cmd (Bwd ProofContext)
getCtx = get

messageUser :: UserMessage -> Cmd ()
messageUser = tell

tellUser :: T.Text -> Cmd ()
tellUser = messageUser . textUserMessage Green

-- TODO put this in a more fitting place
-- Given a proof state command and a context, we can run the command with
-- `runProofState` to produce a message (either the response from the
-- command or the error message) and `Maybe` a new proof context.
runProofState
    :: ProofState a
    -> ProofContext
    -> Either (StackError DInTmRN) (a, ProofContext)
runProofState m loc = runStateT (m `catchStack` catchUnprettyErrors) loc

-- matchTactic' :: TacticFormat -> Text -> Maybe Text
-- matchTactic' (TfKeyword kw) str = T.stripPrefix kw str -- TODO separator
-- matchTactic' (TfAlternative formats) str = foldr (<|>) Nothing
--     (map (`matchTactic'` str) formats)
-- matchTactic' (TfOption format) str = undefined -- XXX this causes branching
-- matchTactic' (TfRepeatZero format) str = do
--     many (matchTactic'

-- instance ToJSRef TacticFormat where
--   toJSRef (TfName a) = [jMacroE|{alt: 'TfKeyword', val: `a`}|]

-- A Cochon tactic consists of:
--
-- * `ctName` - the name of this tactic
-- * `ctDesc` - high level description of the functionality
-- * `ctFormat` - description of the command format for both parsing and
--   contextual help
-- * `ctParse` - parser that parses the arguments for this tactic
-- * `ctxTrans` - state transition to perform for a given list of arguments and
--     current context
-- * `ctHelp` - help text for this tactic

data CochonTactic = CochonTactic
    { ctName    :: Text
    , ctMessage :: Text
    , ctDesc    :: TacticDescription
    , ctxTrans  :: TacticResult -> Cmd ()
    -- TODO(joel) - remove
    , ctHelp    :: TacticHelp
    } deriving Generic

ctParse :: CochonTactic -> Parsley Token TacticResult
ctParse = parseTactic . ctDesc

instance Show CochonTactic where
    show = T.unpack . ctName

instance Eq CochonTactic where
    ct1 == ct2 = ctName ct1 == ctName ct2

instance Ord CochonTactic where
    compare = comparing ctName

-- The help for a tactic is:
-- * a template showing the syntax of the command
-- * an example use
-- * a summary of what the command does
-- * help for each individual argument (yes, they're named)

data TacticHelp = TacticHelp
    { template :: Text -- TODO highlight each piece individually
    , example :: Text
    , summary :: Text

    -- maps from the name of the arg to its help
    -- this is not a map because it's ordered
    , argHelp :: [(Text, Text)]
    }

data Pane = Log | Commands | Settings deriving (Eq, Generic)

data Visibility = Visible | Invisible deriving (Eq, Generic)

toggleVisibility :: Visibility -> Visibility
toggleVisibility Visible = Invisible
toggleVisibility Invisible = Visible

-- A `Command` is a tactic with arguments and the context it operates on. Also
-- the resulting output.

type CTData = (CochonTactic, TacticResult)

data Command = Command
    { commandStr :: Text
    , commandCtx :: Bwd ProofContext

-- Derivative fields - these are less fundamental and can be derived from the
-- first two fields.

    , commandParsed :: Either Text CTData -- is this really necessary?
    , commandOutput :: UserMessage
    } deriving Generic

-- we presently need to be able to add a latest, move to earlier / later, and
-- get the current value

type InteractionHistory = Fwd Command

data CommandFocus
    = InHistory
        { deferred :: Text
        , current :: ListZip Command
        }
    | InPresent Text
    deriving Generic


data EitherOrNot a b
    = JustLeft a
    | JustRight b
    | NotEither


-- TODO _completingTactics would make a nice prism. Used when stowing the
-- current autocomplete state
data AutocompleteState
    = CompletingTactics (ListZip CochonTactic)
    | CompletingParams CochonTactic
    | Welcoming

    -- If the autocomplete is stowed we store its last state so that we can pick
    -- back up there if the user clicks back in.
    | Stowed (EitherOrNot (ListZip CochonTactic) CochonTactic)
    deriving Generic

data InteractionState = InteractionState
    { _proofCtx :: Bwd ProofContext

-- There are two fields dealing with the command history.
--
-- * `_commandFocus` - the user moves around this by pressing the up and down
--   arrows. Up moves back in time and down moves forward in time. Exactly the
--   same as your shell command history. When the user reaches a command they
--   like and starts to edit it, they're instantly moved forward in time to the
--   present.
-- * `_interactions` - a list of all the things the user has ever typed and
--   pigment's responses.

    , _commandFocus :: CommandFocus
    , _interactions :: InteractionHistory
    , _autocomplete :: AutocompleteState

-- Two fields dealing with the right pane (`_currentPane`) is a bit of a
-- misnomer.  It should perhaps be called something like `_currentRightPaneTab`
-- but that's quite cumbersome.

    , _rightPaneVisible :: Visibility
    , _messages :: [UserMessage]
    } deriving (Generic)

$(makeLenses ''InteractionState)

startState :: Bwd ProofContext -> InteractionState
startState pc = InteractionState
    pc
    (InPresent "")
    F0
    (Stowed NotEither)
    Invisible
    []

userInput :: CommandFocus -> Text
userInput (InHistory _ current) =
    let Command str _ _ _ = focus current
    in str
userInput (InPresent str) = str

userInput' :: InteractionState -> Text
userInput' (InteractionState _ _commandFocus _ _ _ _) = userInput _commandFocus
