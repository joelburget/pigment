{-# LANGUAGE OverloadedStrings, TypeFamilies #-}

module Cochon.Controller where

import Control.Applicative
import Control.Monad
import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Foldable as Foldable
import Data.List
import Data.String
import Data.Traversable

import Cochon.CommandLexer
import Cochon.Error
import Cochon.Model
import Cochon.Tactics
import DisplayLang.Lexer
import DisplayLang.Name
import DisplayLang.TmParse
import DisplayLang.DisplayTm
import DisplayLang.PrettyPrint
import DisplayLang.Reactify
import DisplayLang.Scheme
import Distillation.Distiller
import Distillation.Scheme
import Elaboration.Elaborator
import Elaboration.Scheduler
import Elaboration.ElabProb
import Elaboration.ElabMonad
import Elaboration.MakeElab
import Elaboration.RunElab
import Evidences.Eval hiding (($$))
import qualified Evidences.Eval (($$))
import Evidences.Tm
import Kit.BwdFwd
import Kit.ListZip
import Kit.MissingLibrary
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
import Tactics.ShowHaskell
import Tactics.Unification

import Lens.Family2

import Haste hiding (fromString, prompt, focus)
import Haste.Prim
import React hiding (key)
import qualified React

-- The top level page
data Cochon
instance ReactKey Cochon where
    type ClassState Cochon = InteractionState
    type AnimationState Cochon = ()
    type Signal Cochon = Transition

type InteractionReact = React Cochon ()

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

handleSelectPane :: Pane -> MouseEvent -> Maybe Transition
handleSelectPane pane _ = Just $ SelectPane pane

handleToggleRightPane :: MouseEvent -> Maybe Transition
handleToggleRightPane _ = Just ToggleRightPane

handleKey :: KeyboardEvent -> Maybe Transition
handleKey KeyboardEvent{React.key="Enter"}     = Just $ CommandKeypress Enter
handleKey KeyboardEvent{React.key="Tab"}       = Just $ CommandKeypress Tab
handleKey KeyboardEvent{React.key="ArrowUp"}   = Just $ CommandKeypress UpArrow
handleKey KeyboardEvent{React.key="ArrowDown"} = Just $ CommandKeypress DownArrow
handleKey _ = Nothing

handleCmdChange :: ChangeEvent -> Maybe Transition
handleCmdChange = Just . CommandTyping . fromJSStr . targetValue

animDispatch :: Transition
             -> InteractionState
             -> (InteractionState, [AnimConfig Cochon])
animDispatch trans st = (dispatch trans st, [])

dispatch :: Transition -> InteractionState -> InteractionState
dispatch (SelectPane pane) state = state & currentPane .~ pane
dispatch ToggleRightPane state = state & rightPaneVisible %~ toggleVisibility
dispatch (CommandTyping str) state = doCmdChange state str

-- Enter can mean:
-- * complete the currently autocompleted tactic
-- * run the command

-- TODO(joel) maybe run it too if it doesn't take any parameters
dispatch (CommandKeypress Enter)
         state@InteractionState{_autocomplete=(CompletingTactics zip)} =
    completeTactic (focus zip) state
dispatch (CommandKeypress Enter) state = runAndLogCmd state

-- TODO(joel) handle focus here
dispatch (CommandKeypress Tab)
         state@InteractionState{_autocomplete=(CompletingTactics zip)} =
    completeTactic (focus zip) state

dispatch (CommandKeypress UpArrow)
          state@InteractionState{_autocomplete=(CompletingTactics zip)} =
    autocompleteUpArrow state
dispatch (CommandKeypress UpArrow) state = historyUpArrow state

dispatch (CommandKeypress DownArrow)
        state@InteractionState{_autocomplete=(CompletingTactics zip)} =
    autocompleteDownArrow state
dispatch (CommandKeypress DownArrow) state = historyDownArrow state

dispatch _ state = state

autocompleteUpArrow :: InteractionState -> InteractionState
autocompleteUpArrow state = state & autocomplete %~ \auto -> case auto of
    CompletingTactics zip -> case moveEarlier zip of
        Just zip' -> CompletingTactics zip'
        Nothing -> auto
    _ -> auto

-- TODO(joel) prevent cursor from moving to beginning / end

autocompleteDownArrow :: InteractionState -> InteractionState
autocompleteDownArrow state = state & autocomplete %~ \auto -> case auto of
    CompletingTactics zip -> case moveLater zip of
        Just zip' -> CompletingTactics zip'
        Nothing -> auto
    _ -> auto

completeTactic :: CochonTactic -> InteractionState -> InteractionState
completeTactic tac state = state
    & commandFocus .~ InPresent (ctName tac ++ " ")
    & autocomplete .~ CompletingParams tac

historyUpArrow :: InteractionState -> InteractionState
historyUpArrow state = state & commandFocus %~ \hist -> case hist of
        (InHistory _ _) -> case moveEarlier (current hist) of
            Just current' -> hist{current=current'}
            Nothing -> hist
        InPresent str -> case listZipFromFwd (_interactions state) of
            Just listZip -> InHistory str listZip
            Nothing -> hist

historyDownArrow :: InteractionState -> InteractionState
historyDownArrow state = state & commandFocus %~ \hist -> case hist of
        InHistory _ _ -> case moveLater (current hist) of
            Just current' -> hist{current=current'}
            Nothing -> InPresent (deferred hist)
        InPresent str -> hist

runCmd :: Cmd a -> Bwd ProofContext -> (PureReact, Bwd ProofContext)
runCmd cmd ctx =
    let ((_, react), ctx') = runState (runWriterT cmd) ctx
    in (react, ctx')

runAndLogCmd :: InteractionState
             -> InteractionState
runAndLogCmd state =
    let cmdStr = userInput state
        ctx = state^.proofCtx
        parsed = parseCmd cmdStr
        (output, newCtx) = case parsed of
            Left err -> (fromString err, ctx)
            Right (tac, args) -> runCmd (ctxTrans tac args) ctx
        cmd' = Command cmdStr ctx parsed output

    in state & proofCtx .~ newCtx
             & commandFocus .~ InPresent ""
             & interactions %~ (cmd' :>)
             & autocomplete .~ Stowed

doCmdChange :: InteractionState -> String -> InteractionState
doCmdChange state str= state & commandFocus .~ InPresent str
                             & autocomplete .~ findCompletion str

findCompletion :: String -> AutocompleteState
findCompletion str = if ' ' `elem` str
    then let name = head (words str)
         in case find ((== name) . ctName) cochonTactics of
        Nothing -> Stowed
        Just tac -> CompletingParams tac
    else case listZipFromList $ take 10 $ tacticsMatching str of
        Just listZip -> CompletingTactics listZip
        Nothing -> Stowed

parseCmd :: String -> Either String CTData
parseCmd l = case parse tokenize l of
    Left  pf -> Left $ "Tokenize failure: " ++ describePFailure pf id
    Right ts -> case parse pCochonTactic ts of
        Left pf -> Left $
            "Parse failure: " ++
            describePFailure pf (intercalate " " . map crushToken)
        Right ctdata -> Right ctdata

-- The `tacticsMatching` function identifies Cochon tactics that match the
-- given string as a prefix.

tacticsMatching :: String -> [CochonTactic]
tacticsMatching x = filter (isPrefixOf x . ctName) cochonTactics

describePFailure :: PFailure a -> ([a] -> String) -> String
describePFailure (PFailure (ts, fail)) f =
    let errMsg = case fail of
            Abort        -> "parser aborted."
            EndOfStream  -> "end of stream."
            EndOfParser  -> "end of parser."
            Expect t     -> "expected " ++ f [t] ++ "."
            Fail s       -> s
        sucMsg = if length ts > 0
               then "\nSuccessfully parsed: ``" ++ f ts ++ "''."
               else ""
    in errMsg ++ sucMsg

tacticNames :: [CochonTactic] -> String
tacticNames = intercalate ", " . map ctName

pCochonTactic :: Parsley Token CTData
pCochonTactic  = do
    x <- ident <|> (key <$> anyKeyword)
    case tacticsMatching x of
        [ct] -> do
            args <- ctParse ct
            return (ct, trail args)
        [] -> fail "unknown tactic name."
        cts -> fail $
            "ambiguous tactic name (could be " ++ tacticNames cts ++ ")."
