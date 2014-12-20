\begin{code}
module Cochon.Model where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Writer
import Data.Ord
import Data.String

import Cochon.CommandLexer
import DisplayLang.Lexer
import Kit.BwdFwd
import Kit.ListZip
import Kit.Parsley
import ProofState.Edition.ProofContext

import Lens.Family2
import React

-- TODO(joel) - give this a [CochonArg] reader?
type Cmd a = WriterT PureReact (State (Bwd ProofContext)) a

setCtx :: Bwd ProofContext -> Cmd ()
setCtx = put

getCtx :: Cmd (Bwd ProofContext)
getCtx = get

displayUser :: PureReact -> Cmd ()
displayUser = tell

tellUser :: String -> Cmd ()
tellUser = displayUser . fromString
\end{code}

A Cochon tactic consists of:

* `ctName` - the name of this tactic
* `ctParse` - parser that parses the arguments for this tactic
* `ctxTrans` - state transition to perform for a given list of arguments and
    current context
* `ctHelp` - help text for this tactic

\begin{code}
data CochonTactic = CochonTactic
    { ctName   :: String
    , ctParse  :: Parsley Token (Bwd CochonArg)
    , ctxTrans :: [CochonArg] -> Cmd ()
    , ctHelp   :: Either PureReact TacticHelp
    }

instance Show CochonTactic where
    show = ctName

instance Eq CochonTactic where
    ct1 == ct2 =  ctName ct1 == ctName ct2

instance Ord CochonTactic where
    compare = comparing ctName
\end{code}

The help for a tactic is:
* a template showing the syntax of the command
* an example use
* a summary of what the command does
* help for each individual argument (yes, they're named)

\begin{code}
data TacticHelp = TacticHelp
    { template :: PureReact -- TODO highlight each piece individually
    , example :: String
    , summary :: String

    -- maps from the name of the arg to its help
    -- this is not a map because it's ordered
    , argHelp :: [(String, String)]
    }

data Pane = Log | Commands | Settings deriving Eq

data Visibility = Visible | Invisible deriving Eq

toggleVisibility :: Visibility -> Visibility
toggleVisibility Visible = Invisible
toggleVisibility Invisible = Visible
\end{code}

A `Command` is a tactic with arguments and the context it operates on. Also the
resulting output.

\begin{code}
type CTData = (CochonTactic, [CochonArg])

data Command = Command
    { commandStr :: String
    , commandCtx :: (Bwd ProofContext)
\end{code}

Derivative fields - these are less fundamental and can be derived from the
first two fields.

\begin{code}
    , commandParsed :: Either String CTData -- is this really necessary?
    , commandOutput :: PureReact
    }
\end{code}

we presently need to be able to add a latest, move to earlier / later, and get
the current value

\begin{code}
type InteractionHistory = Fwd Command

data CommandFocus
    = InHistory
        { deferred :: String
        , current :: (ListZip Command)
        }
    | InPresent String

data AutocompleteState
    = CompletingTactics (ListZip CochonTactic)
    | CompletingParams CochonTactic
    | Stowed

data InteractionState = InteractionState
    { _proofCtx :: Bwd ProofContext
\end{code}

There are two fields dealing with the command history.

* `_commandFocus` - the user moves around this by pressing the up and down
  arrows. Up moves back in time and down moves forward in time. Exactly the
  same as your shell command history. When the user reaches a command they like
  and starts to edit it, they're instantly moved forward in time to the
  present.
* `_interactions` - a list of all the things the user has ever typed and
  pigment's responses.

\begin{code}
    , _commandFocus :: CommandFocus
    , _interactions :: InteractionHistory
    , _autocomplete :: AutocompleteState
\end{code}

Two fields dealing with the right pane (`_currentPane`) is a bit of a misnomer.
It should perhaps be called something like `_currentRightPaneTab` but that's
quite cumbersome.

\begin{code}
    , _rightPaneVisible :: Visibility
    , _currentPane :: Pane
    }
\end{code}

\begin{code}
startState :: Bwd ProofContext -> InteractionState
startState pc = InteractionState pc (InPresent "") F0 Stowed Visible Log

proofCtx :: Lens' InteractionState (Bwd ProofContext)
proofCtx f state@(InteractionState _proofCtx _ _ _ _ _) =
    (\x -> state{_proofCtx=x}) <$> f _proofCtx

commandFocus :: Lens' InteractionState CommandFocus
commandFocus f state@(InteractionState _ _commandFocus _ _ _ _) =
    (\x -> state{_commandFocus=x}) <$> f _commandFocus

interactions :: Lens' InteractionState InteractionHistory
interactions f state@(InteractionState _ _ _interactions _ _ _) =
    (\x -> state{_interactions=x}) <$> f _interactions

autocomplete :: Lens' InteractionState AutocompleteState
autocomplete f state@(InteractionState _ _ _ _autocomplete _ _) =
    (\x -> state{_autocomplete=x}) <$> f _autocomplete

rightPaneVisible :: Lens' InteractionState Visibility
rightPaneVisible f state@(InteractionState _ _ _ _ _rightPaneVisible _) =
    (\x -> state{_rightPaneVisible=x}) <$> f _rightPaneVisible

currentPane :: Lens' InteractionState Pane
currentPane f state@(InteractionState _ _ _ _ _ _currentPane) =
    (\x -> state{_currentPane=x}) <$> f _currentPane

userInput :: InteractionState -> String
userInput (InteractionState _ _commandFocus _ _ _ _) = case _commandFocus of
    (InHistory _ current) -> let Command str _ _ _ = focus current in str
    InPresent str -> str
\end{code}
