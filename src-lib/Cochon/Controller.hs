{-# LANGUAGE OverloadedStrings, TypeFamilies, LiberalTypeSynonyms,
    PatternSynonyms #-}

module Cochon.Controller where

import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Foldable as Foldable
import Data.List
import Data.String
import Data.Traversable as Traversable

import Lens.Family2

import Cochon.CommandLexer
import Cochon.Model
import Cochon.Tactics
import Cochon.TermController

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
import Tactics.Unification


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

dispatch (ToggleEntry name) state = toggleTerm name state
dispatch (GoTo name) state = goToTerm name state

dispatch (TermTransition (GoToTerm name)) state = goToTerm name state
dispatch (TermTransition (ToggleTerm name)) state = toggleTerm name state

dispatch (TermTransition act) state = termDispatch act state

dispatch _ state = state


toggleTerm :: Name -> InteractionState -> InteractionState
toggleTerm name state@InteractionState{_proofCtx=ctxs :< ctx} =
    case execProofState (toggleEntryVisibility name) ctx of
        Left err ->
            let cmd = messageUser err
                (output, newCtx) = runCmd cmd (state^.proofCtx)
                cmd' = Command "(toggle term)" (ctxs :< ctx)
                               (Left "(no parse)") output
            in state & proofCtx .~ newCtx
                     & interactions %~ (cmd' :>)
        Right ctx' -> state{_proofCtx=ctxs :< ctx'}


goToTerm :: Name -> InteractionState -> InteractionState
goToTerm name state@InteractionState{_proofCtx=ctxs :< ctx} =
    case execProofState (goTo name) ctx of
        Left err ->
            let cmd = messageUser err
                (output, newCtx) = runCmd cmd (state^.proofCtx)
                cmd' = Command "(go to term)" (ctxs :< ctx)
                               (Left "(no parse)") output
            in state & proofCtx .~ newCtx
                     & interactions %~ (cmd' :>)
        Right ctx' -> state{_proofCtx=ctxs :< ctx'}

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

runCmd :: Cmd a -> Bwd ProofContext -> (UserMessage, Bwd ProofContext)
runCmd cmd ctx =
    let ((_, msg), ctx') = runState (runWriterT cmd) ctx
    in (msg, ctx')

runAndLogCmd :: InteractionState -> InteractionState
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
            describePFailure pf (unwords . map crushToken)
        Right ctdata -> Right ctdata

-- The `tacticsMatching` function identifies Cochon tactics that match the
-- given string as a prefix.

tacticsMatching :: String -> [CochonTactic]
tacticsMatching x = filter (isPrefixOf x . ctName) cochonTactics

tacticNamed :: [CochonTactic] -> String -> Maybe CochonTactic
tacticNamed tacs x = find ((== x) . ctName) tacs

describePFailure :: PFailure a -> ([a] -> String) -> String
describePFailure (PFailure (ts, fail)) f =
    let msg = case fail of
            Abort        -> "parser aborted."
            EndOfStream  -> "end of stream."
            EndOfParser  -> "end of parser."
            Expect t     -> "expected " ++ f [t] ++ "."
            Fail s       -> s
        sucMsg = if not (null ts)
               then "\nSuccessfully parsed: ``" ++ f ts ++ "''."
               else ""
    in msg ++ sucMsg

tacticNames :: [CochonTactic] -> String
tacticNames = intercalate ", " . map ctName

pCochonTactic :: Parsley Token CTData
pCochonTactic = pTactic cochonTactics

pTactic :: [CochonTactic] -> Parsley Token CTData
pTactic tacs = do
    x <- ident <|> (key <$> anyKeyword)
    case tacticNamed tacs x of
        Just ct -> do
            args <- parseTactic (ctDesc ct)

            -- trailing semicolons are cool, or not
            -- XXX(joel)
            optional (tokenEq (Keyword KwSemi))

            -- this parser is not gonna be happy if there are args left
            -- over
            return (ct, args)
        Nothing -> fail "unknown tactic name."


data ContextualInfo = InfoHypotheses | InfoContextual
    deriving Eq

data EntryInfo
    = ParamEntry Name INTM
    | DefEntry Name INTM
    | ErrEntryInfo
    deriving Show


-- instance Show EntryInfo where
--     show (ParamEntry name tm) =


infoHypotheses  = infoContextual InfoHypotheses
infoContext     = infoContextual InfoContextual


infoContextual :: ContextualInfo -> ProofState (Bwd EntryInfo)
infoContextual gals = do
    inScope <- getInScope
    bsc <- gets inBScope
    -- holeTy <- optional getHoleGoal
    entries <- Traversable.mapM (entryHelp gals bsc) inScope
    return entries
  where
    entryHelp :: Traversable f
              => ContextualInfo
              -> BScopeContext
              -> Entry f
              -> ProofState EntryInfo
    entryHelp InfoHypotheses bsc p@(EPARAM ref _ k _ _ _) = do
        ty       <- bquoteHere (pty ref)
        return $ ParamEntry (entryName p) ty
    entryHelp InfoContextual bsc d@(EDEF ref _ _ _ _ _ _) = do
        -- ty       <- bquoteHere $ removeShared (paramSpine es) (pty ref)
        ty       <- bquoteHere $ pty ref
        return $ DefEntry (entryName d) (ty)
    entryHelp _ _ _ = return $ ErrEntryInfo

    -- removeShared :: Spine TT REF -> TY -> TY
    -- removeShared []       ty        = ty
    -- removeShared (A (NP r) : as) (PI s t)  = t Evidences.Eval.$$ A (NP r)
