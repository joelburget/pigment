{-# LANGUAGE LiberalTypeSynonyms, DeriveGeneric, TemplateHaskell,
  MultiParamTypeClasses, TypeOperators, OverloadedStrings #-}

module Cochon.Model where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Writer
import Data.Ord
import Data.String
import qualified Data.Text as T
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

data SpecialKey
    = Enter
    | Tab
    | UpArrow
    | DownArrow
    deriving Show

data Transition
    = SelectPane Pane
    | ToggleRightPane
    | CommandKeypress SpecialKey
    | CommandTyping String
    | ToggleEntry Name
    | GoTo Name
    | TermTransition TermAction

data TermAction
    = ToggleTerm Name
    | GoToTerm Name
    | BeginDrag Name
    | ToggleAnnotate Name
    | AnnotationTyping Name T.Text

data MessageSeverity = Green | Orange | Red deriving Show

data UserMessagePart = UserMessagePart
    { messageText :: T.Text
    , relevantName :: Maybe Name
    , stack :: Maybe (StackError DInTmRN)
    , term :: Maybe DInTmRN
    , messageSeverity :: MessageSeverity
    } deriving Show

newtype UserMessage = UserMessage [UserMessagePart] deriving Show

instance IsString UserMessage where
    fromString str = textUserMessage (fromString str)

instance Monoid UserMessage where
    mempty = UserMessage []
    (UserMessage part1) `mappend` (UserMessage part2) = UserMessage (part1 `mappend` part2)

tellTermHere :: (TY :>: INTM) -> ProofState UserMessage
tellTermHere tt = do
    dtm :=>: _ <- distillHere tt
    return (termMessage "told term" dtm)

-- TODO replace these will defaultMessagePart

termMessage :: T.Text -> DInTmRN -> UserMessage
termMessage str tm = UserMessage [UserMessagePart str Nothing Nothing (Just tm) Green]

textUserMessage :: T.Text -> UserMessage
textUserMessage str = UserMessage [UserMessagePart str Nothing Nothing Nothing Green]

stackMessage :: T.Text -> StackError DInTmRN -> UserMessage
stackMessage str stack = UserMessage [UserMessagePart str Nothing (Just stack) Nothing Green]

-- TODO(joel) - give this a TacticResult reader?
type Cmd a = WriterT UserMessage (State (Bwd ProofContext)) a

setCtx :: Bwd ProofContext -> Cmd ()
setCtx = put

getCtx :: Cmd (Bwd ProofContext)
getCtx = get

messageUser :: UserMessage -> Cmd ()
messageUser = tell

tellUser :: T.Text -> Cmd ()
tellUser = messageUser . textUserMessage

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
--     toJSRef a = do
--         obj <- newObj
--         case a of
--             TfKeyword str -> do
--                 setProp "alt" "TfKeyword" obj
--                 setProp "val" (toJSRef str) obj
--             TfAlternative alts -> do
--                 setProp "alt" "TfAlternative" obj
--                 setProp "val" (toJSRef alts) obj
--             TfOption format -> do
--                 setProp "alt" "TfOption" obj
--                 setProp "val" (toJSRef format) obj
--             TfRepeat format -> do
--                 setProp "alt" "TfRepeat" obj
--                 setProp "val" (toJSRef format) obj
--             TfName str -> do
--                 setProp "alt" "TfName" obj
--                 setProp "val" (toJSRef format) obj
--             TfRepeat format -> do
--                 setProp "alt" "TfRepeat" obj
--                 setProp "val" (toJSRef format) obj
--         return obj

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
    { ctName   :: String
    , ctDesc   :: TacticDescription
    , ctxTrans :: TacticResult -> Cmd ()
    -- TODO(joel) - remove
    , ctHelp   :: TacticHelp
    } deriving Generic

ctParse :: CochonTactic -> Parsley Token TacticResult
ctParse = parseTactic . ctDesc

instance Show CochonTactic where
    show = ctName

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
    { template :: String -- TODO highlight each piece individually
    , example :: String
    , summary :: String

    -- maps from the name of the arg to its help
    -- this is not a map because it's ordered
    , argHelp :: [(String, String)]
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
    { commandStr :: String
    , commandCtx :: Bwd ProofContext

-- Derivative fields - these are less fundamental and can be derived from the
-- first two fields.

    , commandParsed :: Either String CTData -- is this really necessary?
    , commandOutput :: UserMessage
    } deriving Generic

-- we presently need to be able to add a latest, move to earlier / later, and
-- get the current value

type InteractionHistory = Fwd Command

data CommandFocus
    = InHistory
        { deferred :: String
        , current :: ListZip Command
        }
    | InPresent String
    deriving Generic

data AutocompleteState
    = CompletingTactics (ListZip CochonTactic)
    | CompletingParams CochonTactic
    | Stowed
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
    , _currentPane :: Pane
    } deriving (Generic)

$(makeLenses ''InteractionState)

startState :: Bwd ProofContext -> InteractionState
startState pc = InteractionState pc (InPresent "") F0 Stowed Invisible Log

userInput :: InteractionState -> String
userInput (InteractionState _ _commandFocus _ _ _ _) = case _commandFocus of
    (InHistory _ current) -> let Command str _ _ _ = focus current in str
    InPresent str -> str
