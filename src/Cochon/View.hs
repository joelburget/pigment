{-# LANGUAGE PatternSynonyms, OverloadedStrings, TypeFamilies,
  MultiParamTypeClasses #-}
module Cochon.View where

import Control.Applicative
import Control.Monad
import Control.Monad.Error
import Control.Monad.State
import qualified Data.Foldable as Foldable
import Data.List
import Data.String
import Data.Traversable
import Data.Void

import Cochon.CommandLexer
import Cochon.Controller
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

import Haste hiding (fromString, prompt, focus)
import Haste.Prim
import Lens.Family2
import React

instance Reactive EntityAnchor where
    reactify x = span_ [ class_ "anchor" ] $ fromString $ show x

page :: InteractionState -> InteractionReact
page state = div_ [ class_ "page" ] $ do
    div_ [ class_ "left-pane" ] $ do
        div_ [ class_ "top-pane" ] $ proofCtxDisplay $ _proofCtx state
        div_ [ class_ "bottom-pane" ] $ do
            locally (autocompleteView (_autocomplete state))
            prompt state
            workingOn state
    rightPane state

-- The autocomplete overlay
data Autocomplete
instance ReactKey Autocomplete where
    type ClassState Autocomplete = AutocompleteState
    type AnimationState Autocomplete = ()
    type Signal Autocomplete = Void

rightPane :: InteractionState -> InteractionReact
rightPane s = do
    when (s^.rightPaneVisible == Visible) (innerRightPane s)
    paneToggle s

paneToggle :: InteractionState -> InteractionReact
paneToggle s = button_ [ class_ "pane-bar"
                       , onClick handleToggleRightPane
                       ] $ do
    let cls = case s^.rightPaneVisible of
          Invisible -> "pane-bar-icon icon ion-arrow-left-b"
          Visible   -> "icon ion-arrow-right-b"
    i_ [ class_ cls ] ""

choosePaneButtons :: Pane -> InteractionReact
choosePaneButtons pane = div_ [ class_ "choose-pane" ] $ do
    let go x = if x == pane then "selected-pane" else ""
    div_ [ class_ (go Log)
         , onClick (handleSelectPane Log)
         ] "Command Log"
    div_ [ class_ (go Commands)
         , onClick (handleSelectPane Commands)
         ] "Commands"
    div_ [ class_ (go Settings)
         , onClick (handleSelectPane Settings)
         ] "Settings"

innerRightPane :: InteractionState -> InteractionReact
innerRightPane InteractionState{_currentPane=pane, _interactions=ixs} =
    div_ [ class_ "right-pane" ] $ do
        choosePaneButtons pane
        locally $ case pane of
            Log -> interactionLog ixs
            Commands -> tacticList
            Settings -> "TODO(joel) - settings"

autocompleteView :: AutocompleteState -> React Autocomplete ()
autocompleteView mtacs = case mtacs of
    Stowed -> ""
    CompletingTactics tacs -> div_ [ class_ "autocomplete" ] $
        innerAutocomplete tacs
    CompletingParams tac -> locally $ case (ctHelp tac) of
        Left react -> div_ [ class_ "tactic-help" ] react
        Right tacticHelp -> longHelp tacticHelp

innerAutocomplete :: ListZip CochonTactic -> React Autocomplete ()
innerAutocomplete (ListZip early focus late) = do
    let desc :: Foldable a => a CochonTactic -> React Autocomplete ()
        desc tacs = Foldable.forM_ tacs (div_ . fromString . ctName)

    desc early

    locally $ div_ [ class_ "autocomplete-focus" ] $ do
        div_ $ fromString $ ctName focus
        div_ $ renderHelp $ ctHelp focus

    desc late

promptArrow :: PureReact
promptArrow = i_ [ class_ "icon ion-ios-arrow-forward" ] ""

prompt :: InteractionState -> InteractionReact
prompt state = div_ [ class_ "prompt" ] $ do
    locally promptArrow
    input_ [ class_ "prompt-input"
           , value_ (toJSStr (userInput state))
           , autofocus_ True
           , onChange handleCmdChange
           , onKeyDown handleKey
           ]

workingOn :: InteractionState -> InteractionReact
workingOn InteractionState{_proofCtx=_ :< loc} = locally $
    div_ [ class_ "working-on" ] $ do
        let runner = do
                mty <- optional' getHoleGoal
                goal <- case mty of
                    Just (_ :=>: ty) -> showGoal ty
                    Nothing          -> return ""

                mn <- optional' getCurrentName
                let name = fromString $ case mn of
                        Just n   -> showName n
                        Nothing  -> ""

                return (goal, name)

        case runProofState runner loc of
            Left err -> err
            Right ((goal, name), loc') -> goal >> name

showGoal :: TY -> ProofState PureReact
showGoal ty@(LABEL _ _) = do
    h <- infoHypotheses
    s <- reactHere . (SET :>:) =<< bquoteHere ty
    return $ div_ [ class_ "goal" ] $ do
        h
        "Programming: "
        s
showGoal ty = do
    s <- reactHere . (SET :>:) =<< bquoteHere ty
    return $ div_ [ class_ "goal" ] $ do
        "Goal: "
        s

interactionLog :: InteractionHistory -> PureReact
interactionLog logs = div_ [ class_ "interaction-log" ] $
    Foldable.forM_ logs $ \(Command cmdStr _ _ out) ->
        div_ [ class_ "log-elem" ] $ do
            div_ [ class_ "log-prompt" ] $ do
                promptArrow
                " "
                fromString cmdStr
            div_ [ class_ "log-output" ] $ out

proofCtxDisplay :: Bwd ProofContext -> InteractionReact
proofCtxDisplay (_ :< ctx) = locally $
    div_ [ class_ "ctx-display" ] $
        case runProofState reactProofState ctx of
            Left err -> err
            Right (display, _) -> display

longHelp :: TacticHelp -> PureReact
longHelp (TacticHelp template example summary args) =
    div_ [ class_ "tactic-help" ] $ do
        div_ [ class_ "tactic-template" ] template

        div_ [ class_ "tactic-example" ] $ do
            div_ [ class_ "tactic-help-title" ] "Example"
            div_ [ class_ "tactic-help-body" ] $ fromString example

        div_ [ class_ "tactic-summary" ] $ do
            div_ [ class_ "tactic-help-title" ] "Summary"
            div_ [ class_ "tactic-help-body" ] $ fromString summary

        Foldable.forM_ args $ \(argName, argSummary) ->
            div_ [ class_ "tactic-arg-help" ] $ do
                div_ [ class_ "tactic-help-title" ] $ fromString argName
                div_ [ class_ "tactic-help-body" ] $ fromString argSummary

renderHelp :: Either PureReact TacticHelp -> PureReact
renderHelp (Left react) = react
renderHelp (Right (TacticHelp _ _ summary _)) = fromString summary

tacticList :: PureReact
tacticList = div_ [ class_ "tactic-list" ] $
    Foldable.forM_ cochonTactics $ \tactic ->
        div_ [ class_ "tactic-info" ] $ renderHelp $ ctHelp tactic

-- The `reactProofState` command generates a reactified representation of
-- the proof state at the current location.
reactProofState :: ProofState PureReact
reactProofState = renderReact

-- Render a bunch of entries!
renderReact :: ProofState PureReact
renderReact = do
    me <- getCurrentName
    es <- replaceEntriesAbove B0
    cs <- putBelowCursor F0
    case (es, cs) of
        (B0, F0) -> reactEmptyTip
        _ -> do
            d <- reactEntries (es <>> F0)
            d' <- case cs of
                F0 -> return d
                _ -> do
                    d'' <- reactEntries cs
                    return (d >> "---" >> d'')
            tip <- reactTip
            putEntriesAbove es
            putBelowCursor cs
            return $ div_ [ class_ "proof-state" ] $ do
                -- div_ [ class_ "entries-name" ] $ do
                --     "Entries name: "
                --     fromString $
                --         case me of
                --             [] -> "(no name)"
                --             _ -> fst $ last me
                div_ [ class_ "proof-state-inner" ] $ d'
                tip

-- reactHereAt
-- replaceEntriesAbove
-- putBelowCursor
-- putEntryAbove

reactEmptyTip :: ProofState PureReact
reactEmptyTip = do
    tip <- getDevTip
    case tip of
        Module -> return $ div_ [ class_ "empty-empty-tip" ]
                                "[empty]"
        _ -> do
            tip' <- reactTip
            return $ div_ [ class_ "empty-tip" ] $
                reactKword KwDefn >> " " >> tip'

reactEntries :: Fwd (Entry Bwd) -> ProofState PureReact
reactEntries F0 = return ""
reactEntries (e :> es) = do
    putEntryAbove e
    (>>) <$> reactEntry e <*> reactEntries es

reactEntry :: Entry Bwd -> ProofState PureReact
reactEntry (EPARAM (_ := DECL :<: ty) (x, _) k _ anchor)  = do
    ty' <- bquoteHere ty
    tyd <- reactHereAt (SET :>: ty')
    return $ reactBKind k $ div_ [ class_ "entry" ] $ do
        div_ [ class_ "tm-name" ] $ fromString x
        -- TODO(joel) - show anchor in almost same way as below?
        reactKword KwAsc
        div_ [ class_ "ty" ] tyd
reactEntry e = do
    goIn
    d <- renderReact
    goOut
    return $ div_ [ class_ "entry" ] $ do
        div_ [ class_ "tm-name" ] $ fromString (fst (entryLastName e))
        -- div_ [ class_ "anchor" ] $ do
        --     "[["
        --     reactify $ entryAnchor e
        --     "]]"
        d

-- “Developments can be of different nature: this is indicated by the Tip”

reactTip :: ProofState PureReact
reactTip = do
    tip <- getDevTip
    case tip of
        Module -> return $ div_ [ class_ "tip" ] $ "(module)"
        Unknown (ty :=>: _) -> do
            hk <- getHoleKind
            tyd <- reactHere (SET :>: ty)
            return $ div_ [ class_ "tip" ] $ do
                reactHKind hk
                reactKword KwAsc
                tyd
        Suspended (ty :=>: _) prob -> do
            hk <- getHoleKind
            tyd <- reactHere (SET :>: ty)
            return $ div_ [ class_ "tip" ] $ do
                fromString $ "(SUSPENDED: " ++ show prob ++ ")"
                reactHKind hk
                reactKword KwAsc
                tyd
        Defined tm (ty :=>: tyv) -> do
            tyd <- reactHere (SET :>: ty)
            tmd <- reactHereAt (tyv :>: tm)
            return $ div_ [ class_ "tip" ] $
                (tmd >> reactKword KwAsc >> tyd)

reactHKind :: HKind -> PureReact
reactHKind kind = span_ [ class_ "hole" ] $ case kind of
    Waiting    -> "?"
    Hoping     -> "HOPE?"
    (Crying s) -> fromString ("CRY <<" ++ s ++ ">>")
