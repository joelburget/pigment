{-# LANGUAGE PatternSynonyms, OverloadedStrings, TypeFamilies,
  MultiParamTypeClasses, LambdaCase, LiberalTypeSynonyms, DataKinds,
  NamedFieldPuns, TypeOperators #-}

module Cochon.View where

import Control.Applicative
import Control.Monad as Monad
import Control.Monad.State
import qualified Data.Foldable as Foldable
import Data.Monoid
import Data.List
import Data.String
import Data.Traversable as Traversable
import Data.Void

import GHCJS.Foreign
import GHCJS.Types
import Lens.Family2
import React hiding (label_)
import React.MaterialUI

import Cochon.CommandLexer
import Cochon.Controller
import Cochon.TermController
import Cochon.Error
import Cochon.Model
import Cochon.Tactics
import Cochon.Reactify
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
import Kit.Parsley
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
import Tactics.SpecialTactics
import Tactics.Unification

import Kit.Trace


instance Reactive EntityAnchor where
    reactify x = span_ [ class_ "anchor" ] $ fromString $ show x


page :: InteractionState -> InteractionReact
page state = div_ [ class_ "page" ] $ do
    div_ [ class_ "left-pane" ] $ do
        div_ [ class_ "top-pane" ] $ do
            -- div_ [ class_ "ctx-layers" ] $
            --     proofCtxLayers (pcLayers (_proofCtx state))
            -- elabTrace (show (_proofCtx state))
            -- elabTrace (renderHouseStyle (pretty (_proofCtx state) maxBound))

            proofCtxDisplay $ _proofCtx state

        div_ [ class_ "bottom-pane" ] $ do
            locally $ autocompleteView (_autocomplete state)
            prompt state
    rightPane state


-- The autocomplete overlay
type Autocomplete a = a AutocompleteState Void ()


-- proofCtxLayers :: Bwd Layer -> InteractionReact
-- proofCtxLayers layers = ol_ $ Foldable.forM_ layers $ \layer ->
--     li_ "layer"


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


autocompleteView :: AutocompleteState -> Autocomplete React'
autocompleteView mtacs = case mtacs of
    Stowed -> ""
    CompletingTactics tacs -> div_ [ class_ "autocomplete" ] $
        innerAutocomplete tacs
    CompletingParams tac -> locally $ case ctHelp tac of
        Left react -> div_ [ class_ "tactic-help" ] react
        Right tacticHelp -> longHelp tacticHelp


innerAutocomplete :: ListZip CochonTactic -> Autocomplete React'
innerAutocomplete (ListZip early focus late) = do
    let desc :: Foldable a => a CochonTactic -> Autocomplete React'
        desc tacs = Foldable.forM_ tacs (div_ . fromString . ctName)

    desc early

    locally $ div_ [ class_ "autocomplete-focus" ] $ do
        div_ $ fromString $ ctName focus
        div_ $ renderHelp $ ctHelp focus

    desc late


promptArrow :: Pure React'
promptArrow = i_ [ class_ "icon ion-ios-arrow-forward" ] ""


prompt :: InteractionState -> InteractionReact
prompt state = div_ [ class_ "prompt" ] $ do
    locally promptArrow
    input_ [ class_ "prompt-input"
           , value_ (toJSString (userInput state))
           , autofocus_ True
           , onChange handleCmdChange
           , onKeyDown handleKey
           ]


showEntry :: Entry f -> Bool
showEntry (EEntity _ _ _ _ AnchNo _) = True
showEntry _ = True


getUsefulTactics :: ProofState [SpecialTactic]
getUsefulTactics = do
    (assumption >> return [assumptionTac]) <|> return []


showTactics :: [SpecialTactic] -> InteractionReact
showTactics tacs = ul_ [ class_ "useful-tactics" ] $ case tacs of
    [] -> li_ "none found :("
    _  -> Foldable.mapM_ showTactic tacs


showTactic :: SpecialTactic -> InteractionReact
showTactic (SpecialTactic action name description) = li_ [ class_ "special-tactic" ] $ do
    flatButton
        [ class_ "special-tactic-button"
        , label_ (fromString name)
        , onClick (\_ -> handleRunTactic action)
        ] $ return ()
    fromString description


prettyDevView :: Traversable f => ProofContext -> Dev f -> InteractionReact
prettyDevView loc (Dev entries tip _ suspended) =
    let runner :: ProofState (TermReact, TermReact, InteractionReact)
        runner = do
            tipViewed <- tipView tip
            entries <- getEntriesAbove
            usefulTactics <- getUsefulTactics
            let entriesWeCareAbout = filter showEntry $ Foldable.toList entries
                entriesViewed = Foldable.forM_
                    entriesWeCareAbout
                    (entryView loc)
                -- -- Only show entries in a module. They're shown already
                -- entriesViewed' = case tip of
                --     Module -> ""
                --     _ -> entriesViewed
            return (tipViewed, entriesViewed, showTactics usefulTactics)
        inner :: InteractionReact
        inner = case runProofState runner loc of
            Left err -> locally err
            Right ((tipViewed, entriesViewed, usefulTactics), _) -> do
                div_ [ class_ "dev-header" ] $
                    div_ [ class_ "dev-header-tip" ] (locally tipViewed)
                div_ [ class_ "dev-entries-container" ] $ do
                    div_ [ class_ "dev-entries-header" ] "in scope:"
                    ol_ [ class_ "dev-entries" ] (locally entriesViewed)
                div_ [ class_ "dev-tactics" ] $ do
                    div_ [ class_ "dev-tactics-header" ] "applicable tactics:"
                    usefulTactics

    in div_ [ class_ "dev" ] inner


workingOn :: ProofContext -> InteractionReact
workingOn loc =
    let runner :: ProofState InteractionReact
        runner = do
            mty <- optional getHoleGoal
            case mty of
                Just (_ :=>: ty) -> workingOn' ty
                Nothing          -> return ""

        val :: InteractionReact
        val = case runProofState runner loc of
            -- TODO(joel) isn't there something to abstract out this error
            -- handling? is it repeated in a few places? should we be
            -- running the proof state just once?
            Left err -> locally err
            Right (goal, _) -> goal

    in val


workingOn' :: TY -> ProofState InteractionReact
workingOn' ty@(LABEL _ _) = do
    inScope <- infoInScope
    hypotheses <- infoHypotheses
    context <- infoContext
    goal <- reactHere . (SET :>:) =<< bquoteHere ty

    return $ div_ [ class_ "working-on" ] $ do
        -- div_ [ class_ "goal-inscope" ] $ do
        --     div_ "in scope: "
        --     ul_ [ class_ "goal-inscope-list" ] inScope
        div_ [ class_ "goal-hypotheses" ] $ do
            div_ [ class_ "goal-hypotheses-header" ] "in scope: "
            div_ hypotheses
        -- div_ [ class_ "goal-context" ] $ do
        --     div_ "context: "
        --     div_ context
        -- div_ [ class_ "goal-body" ] $ do
        --     div_ [ class_ "goal-body-header" ] "working on"
        --     locally $ div_ goal

workingOn' ty = do
    goal <- reactHere . (SET :>:) =<< bquoteHere ty
    return $ div_ [ class_ "goal" ] $ do
        div_ [ class_ "goal-header" ] "Goal:"
        div_ [ class_ "goal-body" ] (locally goal)


infoInScope :: ProofState InteractionReact
infoInScope = do
    pc <- get
    inScope <- getInScope
    return (locally (reactEntries' (inBScope pc) inScope))


reactEntries' :: (Traversable f, Traversable g)
              => BScopeContext
              -> f (Entry g)
              -> TermReact
reactEntries' bsc fs = Foldable.forM_ fs $ \entry ->
    -- TODO(joel) what is this even doing?
    case entryRef entry of
        Just ref -> li_ $ paramEntryView entry
        Nothing -> return ()



reactEntriesAbs :: Traversable f => f (Entry f) -> TermReact
reactEntriesAbs = div_ . Foldable.foldMap f
  where f e = fromString (showName (entryName e))


-- The `reactBKind` function reactifies a `ParamKind` if supplied with an
-- element representing its name and type.
reactBKind :: ParamKind -> React a b c () -> React a b c ()
reactBKind ParamLam  d = reactKword KwLambda >> d >> reactKword KwArr
reactBKind ParamAll  d = reactKword KwLambda >> d >> reactKword KwImp
reactBKind ParamPi   d = "(" >> d >> ")" >> reactKword KwArr


data ContextualInfo = InfoHypotheses | InfoContextual
    deriving Eq


infoHypotheses  = infoContextual InfoHypotheses
infoContext     = infoContextual InfoContextual


infoContextual :: ContextualInfo -> ProofState InteractionReact
infoContextual gals = do
    inScope <- getInScope
    bsc <- gets inBScope
    -- holeTy <- optional getHoleGoal
    entries <- Traversable.mapM (entryHelp gals bsc) inScope
    return $ ul_ [ class_ "info-contextual" ] $ Foldable.sequence_ entries
  where
    entryHelp :: Traversable f
              => ContextualInfo
              -> BScopeContext
              -> Entry f
              -> ProofState InteractionReact
    entryHelp InfoHypotheses bsc p@(EPARAM ref _ k _ _ _) = do
        ty       <- bquoteHere (pty ref)
        reactTy  <- reactHere (SET :>: ty)
        return $ locally $ li_ [ class_ "param-entry" ] $ do
            paramEntryView p
            div_ [ class_ "param-entry-asc" ] $ do
                reactKword KwAsc
                reactTy
    entryHelp InfoContextual bsc d@(EDEF ref _ _ _ _ _ _) = do
        -- ty       <- bquoteHere $ removeShared (paramSpine es) (pty ref)
        ty       <- bquoteHere $ pty ref
        reactTy  <- reactHere (SET :>: ty)
        return $ locally $ li_ [ class_ "def-entry" ] $ do
            fromString $ showRelName $ christenREF bsc ref
            reactKword KwAsc
            reactTy
    entryHelp _ _ _ = return $ return ()

    -- paramEntry :: Traversable f => Entry f -> TermReact
    -- paramEntry (EPARAM ref _ k _ _ _) = div_ [ class_ "param-entry" ] $ do
    --     reactBKind k $ do
    --         fromString $ showRelName $ christenREF bsc ref
    --         reactKword KwAsc
    --         reactTy

    -- defEntry :: Traversable f => Entry f -> TermReact
    -- defEntry (EDEF ref _ _ _ _ _ _) = div_ [ class_ "def-entry" ] $ do
    --     fromString $ showRelName $ christenREF bsc ref
    --     reactKword KwAsc
    --     reactTy

    removeShared :: Spine TT REF -> TY -> TY
    removeShared []       ty        = ty
    removeShared (A (NP r) : as) (PI s t)  = t Evidences.Eval.$$ A (NP r)


interactionLog :: InteractionHistory -> Pure React'
interactionLog logs = div_ [ class_ "interaction-log" ] $
    Foldable.forM_ logs $ \(Command cmdStr _ _ out) ->
        div_ [ class_ "log-elem" ] $ do
            div_ [ class_ "log-prompt" ] $ do
                promptArrow
                " "
                fromString cmdStr
            div_ [ class_ "log-output" ] out


proofCtxDisplay :: Bwd ProofContext -> InteractionReact
proofCtxDisplay (_ :< ctx) = div_ [ class_ "ctx-display" ] $
    proofContextView ctx


longHelp :: TacticHelp -> Pure React'
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


renderHelp :: Either (Pure React') TacticHelp -> Pure React'
renderHelp (Left react) = react
renderHelp (Right (TacticHelp _ _ summary _)) = fromString summary


tacticList :: Pure React'
tacticList = div_ [ class_ "tactic-list" ] $
    Foldable.forM_ cochonTactics $ \tactic ->
        li_ [ class_ "tactic-info" ] $ renderHelp $ ctHelp tactic


numEntries :: Layer -> Int
numEntries (Layer aboveEntries _ belowEntries _ _ _) =
    foldableSize aboveEntries + 1 + foldableSize belowEntries


layerView :: Layer -> InteractionReact
layerView layer@(Layer aboveEntries currentEntry belowEntries tip _ suspend) =
    div_ [ class_ "layer" ] $ do
        flatButton
            [ class_ "layer-button"
            , label_ (reasonableName currentEntry)
            , onClick (handleGoTo (currentEntryName currentEntry)) ] $
                return ()
        locally $ div_ [ class_ "layer-info" ] $ do
            -- XXX(joel) this size is about the layer outside this one?
            -- fromString $ "size: " ++ show (numEntries layer)
            suspendView suspend


reasonableName :: CurrentEntry -> JSString
reasonableName = fromString . fst . last . currentEntryName


entryReasonableName :: Traversable f => Entry f -> JSString
entryReasonableName = fromString . fst . last . entryName


-- currentEntryView :: CurrentEntry -> Pure React'
-- currentEntryView entry@(CDefinition _ _ _ _ _ expanded _) =
--     div_ [ class_ "current-entry cdefinition" ] $
--         reasonableName entry
-- currentEntryView entry@(CModule _ expanded purpose _) =
--     div_ [ class_ "current-entry cmodule" ] $
--         reasonableName entry


paramEntryView :: Traversable f => Entry f -> TermReact
paramEntryView entry@(EEntity _ _ entity term _ _) =
    -- let cls = if term `matchesGoal` goal
    --           then "matches-goal"
    --           else ""
    div_ $ text_ $ entryReasonableName entry
    -- div_ [ class_ "entry"
    --      , onClick (handleEntryGoTo (entryName entry))
    --      -- ] $ fromString $ showRelName $ christenREF bsc ref
    --      ] $
    --     div_ [ class_ "entity" ] $
    --         flatButton
    --             [ label_ (entryReasonableName entry)
    --             , onClick (handleEntryGoTo (entryName entry))
    --             ] $ return ()
paramEntryView mod = div_ $ do
    text_ $ fromString $ showName $ entryName mod
    " (module)" -- TODO(joel) I don't know what to show
    let entries = Foldable.toList (devEntries (dev mod))
    ol_ [ class_ "dev-entries" ] $
        Foldable.forM_ entries collapsedEntry


-- TODO(joel) think about how to guarantee an ol_'s children are li_'s

entryView :: Traversable f => ProofContext -> Entry f -> TermReact
entryView pc entry@(EEntity _ _ entity term anchor meta) = li_ $
    div_ [ class_ "entry" ] $ if meta^.expanded
        then expandedEntry pc entry
        else collapsedEntry entry
entryView _ entry@(EModule _ dev purpose _) = li_ $
    div_ [ class_ "module" ] $ do
        flatButton
            [ label_ (entryReasonableName entry)
            , onClick (handleEntryToggle (entryName entry)) ] $
                return ()
        div_ $ do
            span_ "(module)"
            span_ $ fromString $ "purpose: " ++ showPurpose purpose


-- TODO(joel)
-- * The first expandedEntry case below is weird - maybe inline this?
dataRunner :: Traversable f => ProofContext -> Entry f -> TermReact
dataRunner ctx entry@(EEntity _ _ (Definition LETG dev) _ AnchDataDef _) = do
    let entries = Foldable.toList (devEntries dev)
    div_ [ class_ "data-entry" ] $ do
       div_ [ class_ "data-header" ] $ do
           div_ [ class_ "data-name" ] $ do
               "data "
               text_ $ entryReasonableName entry
           let params = filter paramDecl entries
           ul_ [ class_ "data-params" ] $ Foldable.forM_ params $
               -- TODO(joel) have paramDecl return the name
               \entry@(EEntity _ _ _ _ (AnchParTy name) _) -> li_ $
                   reactBrackets Round $ do
                       fromString name
                       ": "
                       expandedEntry' ctx entry
       ol_ [ class_ "data-entries" ] $
           let constrs = filter dataConDecl entries
           -- in Foldable.forM_ entries $ li_ . expandedEntry' ctx
           in Foldable.forM_ constrs $ \entry -> do
               elabTrace ("entry anchor: " ++ show (entryAnchor entry))
               li_ $ expandedEntry' ctx entry

       -- Also show:
       -- * Induction Scheme

       div_ [ class_ "data-controls" ] $ do
           flatButton
               [ label_ "add constructor"
               , onClick (handleAddConstructor (entryName entry))
               ] $ return ()
           flatButton
               [ label_ "toggle annotation"
               , onClick (handleToggleAnnotate (entryName entry))
               ] $ return ()

       div_ [ class_ "data-meta" ] $ do
           input_ [ value_ "metadata!!" ]

dataRunner _ _ = error "unexpected non-data-development"


termRunner :: INTM -> ProofState TermReact
termRunner term = reactHere (SET :>: term)


-- Show an entry without the collapse button
expandedEntry' :: Traversable f => ProofContext -> Entry f -> TermReact
expandedEntry' ctx entry@EEntity{term} =
    case runProofState (termRunner term) ctx of
        Left err -> err
        Right (view, _) -> view


-- Show an expanded entry with the collapse button
expandedEntry :: Traversable f => ProofContext -> Entry f -> TermReact
expandedEntry ctx entry@(EEntity _ _ (Definition LETG dev) _ AnchDataDef _) =
    dataRunner ctx entry
expandedEntry ctx entry@EEntity{term} =
    div_ [ class_ "expanded-entry" ] $ do
        flatButton
            [ label_ "collapse"
            , onClick (handleEntryToggle (entryName entry))
            ] $ return ()
        div_ $ do
            text_ $ entryReasonableName entry
            reactKword KwAsc
        expandedEntry' ctx entry
expandedEntry _ _ = return ()


collapsedEntry :: Traversable f => Entry f -> TermReact
collapsedEntry entry = flatButton
    [ label_ (entryReasonableName entry)
    , onClick (handleEntryToggle (entryName entry)) ] $
        return ()


-- class Classes a where
--     classes_ :: JSString -> a

-- instance Classes (AttrOrHandler b) where
--     classes_ = class_

-- instance Classes a => Classes (a -> AttrOrHandler b) where
--     classes_ x =


suspendView :: SuspendState -> Pure React'
suspendView state =
    let (elem, cls) = case state of
            SuspendNone -> ("not suspended", "none")
            SuspendStable -> ("suspended (stable)", "stable")
            SuspendUnstable -> ("suspended (unstable!)", "unstable")

    in div_ [ class_ (fromString ("suspend-state " ++ cls)) ] elem


tipView :: Tip -> ProofState TermReact
tipView Module = do
    name <- getCurrentName
    return $ div_ [ class_ "tip" ] $ fromString $ fst $ last name -- HACK(joel)
tipView (Unknown (ty :=>: _)) = do
    hk <- getHoleKind
    tyd <- reactHere (SET :>: ty)
    x <- prettyHere (SET :>: ty)
    elabTrace $ renderHouseStyle x
    return $ do
        div_ [ class_ "tip-programming" ] "make this:"
        div_ [ class_ "tip" ] $ do
            reactHKind hk
            reactKword KwAsc
            tyd
tipView (Suspended (ty :=>: _) prob) = do
    hk <- getHoleKind
    tyd <- reactHere (SET :>: ty)
    x <- prettyHere (SET :>: ty)
    elabTrace $ renderHouseStyle x
    return $ div_ [ class_ "tip" ] $ do
        div_ [ class_ "tip-suspended" ] $ fromString $
            "(SUSPENDED: " ++ show prob ++ ")"
        reactHKind hk
        reactKword KwAsc
        tyd
tipView (Defined tm (ty :=>: tyv)) = do
    tyd <- reactHere (SET :>: ty)
    tmd <- reactHere (tyv :>: tm)

    x <- prettyHere (SET :>: ty)
    y <- prettyHere (tyv :>: tm)
    elabTrace $ renderHouseStyle x
    elabTrace $ renderHouseStyle y
    return $ div_ [ class_ "tip" ] $ do
        tmd
        reactKword KwAsc
        tyd


proofContextView :: ProofContext -> InteractionReact
proofContextView pc@(PC layers aboveCursor belowCursor) =
    div_ [ class_ "proof-context" ] $ do
        div_ [ class_ "proof-context-layers" ] $ do
            h2_ "layers"
            -- TODO(joel) - disable current layer
            ol_ $ do
                -- TODO(joel) - this is hacky - remove duplication in
                -- layerView
                div_ [ class_ "layer first-layer" ] $
                    flatButton
                        [ class_ "layer-button"
                        , label_ "root"
                        , onClick (handleGoTo []) ] $
                            return ()
                Foldable.forM_ layers layerView
        -- workingOn pc
        -- if foldableSize layers == 0
        --     then "(root module)"
        --     else "(non-root module)"
        prettyDevView pc aboveCursor



dataConDecl :: Entry a -> Bool
dataConDecl (EEntity _ _ _ _ (AnchConName _) _) = True
-- dataConDecl (EEntity _ _ _ _ AnchConDescs _) = True
dataConDecl _ = False


paramDecl :: Entry a -> Bool
paramDecl (EEntity _ _ _ _ (AnchParTy name) _) = True
paramDecl _ = False


-- "Developments can be of different nature: this is indicated by the Tip"


reactHKind :: HKind -> React a b c ()
reactHKind kind = span_ [ class_ "hole" ] $ case kind of
    Waiting    -> "?"
    Hoping     -> "HOPE?"
    (Crying s) -> fromString ("CRY <<" ++ s ++ ">>")
