{-# LANGUAGE LiberalTypeSynonyms, DeriveGeneric, TemplateHaskell,
  MultiParamTypeClasses #-}

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
import Kit.BwdFwd
import Kit.ListZip
import Kit.Parsley
import NameSupply.NameSupply
import ProofState.Edition.ProofContext

import Lens.Family2
import Lens.Family2.TH
import React

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
    = ExpandTerm Name
    | GoToTerm Name
    | BeginDrag Name

-- The top level page
type Cochon a = a InteractionState Transition ()
type InteractionReact = Cochon React'

type ReactTerm a = a ProofContext TermAction ()
type TermReact = ReactTerm React'

instance GeneralizeSignal TermAction Transition where
    generalizeSignal = TermTransition

-- TODO(joel) - give this a [CochonArg] reader?
type Cmd a = WriterT (Pure React') (State (Bwd ProofContext)) a

setCtx :: Bwd ProofContext -> Cmd ()
setCtx = put

getCtx :: Cmd (Bwd ProofContext)
getCtx = get

displayUser :: Pure React' -> Cmd ()
displayUser = tell

tellUser :: String -> Cmd ()
tellUser = displayUser . fromString

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
    , ctDesc   :: TacticFormat
    -- TODO(joel) - remove
    , ctParse  :: Parsley Token (Bwd CochonArg)
    , ctxTrans :: [CochonArg] -> Cmd ()
    -- TODO(joel) - remove
    , ctHelp   :: Either (Pure React') TacticHelp
    } deriving Generic

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
    { template :: Pure React' -- TODO highlight each piece individually
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

type CTData = (CochonTactic, [CochonArg])

data Command = Command
    { commandStr :: String
    , commandCtx :: Bwd ProofContext

-- Derivative fields - these are less fundamental and can be derived from the
-- first two fields.

    , commandParsed :: Either String CTData -- is this really necessary?
    , commandOutput :: Pure React'
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
