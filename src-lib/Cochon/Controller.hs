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
import Data.Monoid
import Data.String
import Data.Text (Text)
import qualified Data.Text as T
import Data.Traversable as Traversable

import Lens.Family2

import Cochon.Model
import Cochon.Tactics
import Cochon.TermController

import DisplayLang.Name
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

import Kit.Trace
import Debug.Trace


dispatch :: Transition -> InteractionState -> InteractionState

-- dispatch (ToggleEntry name) state = toggleTerm name state
-- dispatch (GoTo name) state = goToTerm name state

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
            in state & proofCtx .~ newCtx
        Right ctx' -> state{_proofCtx=ctxs :< ctx'}


goToTerm :: Name -> InteractionState -> InteractionState
goToTerm name state@InteractionState{_proofCtx=ctxs :< ctx} =
    case execProofState (goTo name) ctx of
        Left err ->
            let cmd = messageUser err
                (output, newCtx) = runCmd cmd (state^.proofCtx)
            in state & proofCtx .~ newCtx
        Right ctx' -> state{_proofCtx=ctxs :< ctx'}



runCmd :: Cmd a -> Bwd ProofContext -> (UserMessage, Bwd ProofContext)
runCmd cmd ctx =
    let ((_, msg), ctx') = runState (runWriterT cmd) ctx
    in (msg, ctx')


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
    entryHelp InfoHypotheses _ p@(EPARAM ref _ k _ _ _) = do
        -- ty       <- mQuote (pty ref)
        return $ ParamEntry (entryName p) (pty ref)
    entryHelp InfoContextual _ d@(EDEF ref _ _ _ _ _ _) = do
        -- ty       <- mQuote $ removeShared (paramSpine es) (pty ref)
        return $ DefEntry (entryName d) (pty ref)
    entryHelp _ _ _ = return $ ErrEntryInfo

    -- removeShared :: Spine TT REF -> TY -> TY
    -- removeShared []       ty        = ty
    -- removeShared (A (NP r) : as) (PI s t)  = t Evidences.Eval.$$ A (NP r)
