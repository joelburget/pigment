Cochon (Command-line Interface)
===============================

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs,
>     DeriveFunctor, DeriveFoldable, DeriveTraversable, OverloadedStrings,
>     CPP, NamedFieldPuns #-}

> module Cochon.Cochon where

> import Control.Applicative
> import Control.Monad.Except
> import Control.Monad.State
> import Control.Monad.Writer
> import Data.Foldable as Foldable
> import Data.List hiding (find)
> import Data.Monoid
> import Data.Ord
> import Data.String
> import Data.Traversable

> import NameSupply.NameSupply
> import Evidences.Eval hiding (($$))
> import qualified Evidences.Eval (($$))
> import Evidences.Tm hiding (In)

> import DisplayLang.Lexer
> import DisplayLang.Name
> import DisplayLang.TmParse
> import DisplayLang.DisplayTm
> import DisplayLang.PrettyPrint
> import DisplayLang.Reactify
> import DisplayLang.Scheme

> import ProofState.Edition.ProofContext
> import ProofState.Edition.ProofState
> import ProofState.Edition.Entries
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation
> import ProofState.Edition.Scope

> import ProofState.Interface.Search
> import ProofState.Interface.ProofKit
> import ProofState.Interface.Lifting
> import ProofState.Interface.Module
> import ProofState.Interface.NameResolution
> import ProofState.Interface.Solving
> import ProofState.Interface.Parameter

> import ProofState.Structure.Developments
> import ProofState.Structure.Entries

> import Tactics.Elimination
> import Tactics.PropositionSimplify
> import Tactics.ProblemSimplify
> import Tactics.Data
> import Tactics.IData
> import Tactics.Relabel
> import Tactics.ShowHaskell
> import Tactics.Matching
> import Tactics.Unification

> import Elaboration.Elaborator
> import Elaboration.Scheduler
> import Elaboration.ElabProb
> import Elaboration.ElabMonad
> import Elaboration.MakeElab
> import Elaboration.RunElab

> import Distillation.Distiller
> import Distillation.Scheme
> import Cochon.CommandLexer
> import Cochon.Error
> import Kit.BwdFwd
> import Kit.Parsley
> import Kit.MissingLibrary
>
> import Haste hiding (fromString, prompt, focus)
> import Haste.JSON
> import Haste.Prim
> import Lens.Family2
> import Lens.Family2.Stock
> import React hiding (key)
> import qualified React

Here we have a very basic command-driven interface to the proof state
monad.

> infoInScope :: ProofState PureReact
> infoInScope = do
>     pc <- get
>     inScope <- getInScope
>     return (fromString (showEntries (inBScope pc) inScope))

> infoDump :: ProofState PureReact
> infoDump = gets (fromString . show)

The `infoElaborate` command calls `elabInfer` on the given neutral
display term, evaluates the resulting term, bquotes it and returns a
pretty-printed string representation. Note that it works in its own
module which it discards at the end, so it will not leave any subgoals
lying around in the proof state.

> infoElaborate :: DExTmRN -> ProofState PureReact
> infoElaborate tm = draftModule "__infoElaborate" $ do
>     (tm' :=>: tmv :<: ty) <- elabInfer' tm
>     tm'' <- bquoteHere tmv
>     s <- reactHere (ty :>: tm'')
>     return s

The `infoInfer` command is similar to `infoElaborate`, but it returns a
string representation of the resulting type.

> infoInfer :: DExTmRN -> ProofState PureReact
> infoInfer tm = draftModule "__infoInfer" $ do
>     (_ :<: ty) <- elabInfer' tm
>     ty' <- bquoteHere ty
>     s <- reactHere (SET :>: ty')
>     return s

The `infoContextual` command displays a distilled list of things in the
context, parameters if the argument is False or definitions if the
argument is True.

> infoHypotheses  = infoContextual False
> infoContext     = infoContextual True

> infoContextual :: Bool -> ProofState PureReact
> infoContextual gals = do
>     inScope <- getInScope
>     bsc <- gets inBScope
>     d <- help bsc inScope
>     return d
>   where
>     help :: BScopeContext -> Entries -> ProofState PureReact
>     help bsc B0 = return ""
>     help bsc (es :< EPARAM ref _ k _ _) | not gals = do
>         ty       <- bquoteHere (pty ref)
>         reactTy  <- reactHereAt (SET :>: ty)
>         d        <- help bsc es
>         return $ do
>             d
>             reactBKind k $ do
>                 fromString $ showRelName $ christenREF bsc ref
>                 reactKword KwAsc
>                 reactTy
>     help bsc (es :< EDEF ref _ _ _ _ _) | gals = do
>         ty       <- bquoteHere $ removeShared (paramSpine es) (pty ref)
>         reactTy  <- reactHere (SET :>: ty)
>         d        <- help bsc es
>         return $ do
>             d
>             fromString $ showRelName $ christenREF bsc ref
>             reactKword KwAsc
>             reactTy
>     help bsc (es :< _) = help bsc es
>     removeShared :: Spine {TT} REF -> TY -> TY
>     removeShared []       ty        = ty
>     removeShared (A (NP r) : as) (PI s t)  = t Evidences.Eval.$$ A (NP r)

This old implementation is written using a horrible imperative hack that
saves the state, throws away bits of the context to produce an answer,
then restores the saved state. We can get rid of it once we are
confident that the new version (above) produces suitable output.

> infoContextual' :: Bool -> ProofState PureReact
> infoContextual' gals = do
>     save <- get
>     let bsc = inBScope save
>     me <- getCurrentName
>     ds <- many' (hypsHere bsc me <* optional' killBelow <* goOut <* removeEntryAbove)
>     d <- hypsHere bsc me
>     put save
>     return $ Foldable.sequence_ $ d:reverse ds
>  where
>    hypsHere :: BScopeContext -> Name -> ProofState PureReact
>    hypsHere bsc me = do
>        es <- getEntriesAbove
>        d <- hyps bsc me
>        putEntriesAbove es
>        return d
>    killBelow = do
>        l <- getLayer
>        replaceLayer (l { belowEntries = NF F0 })
>    hyps :: BScopeContext -> Name -> ProofState PureReact
>    hyps bsc me = do
>        es <- getEntriesAbove
>        case (gals, es) of
>            (_, B0) -> return ""
>            (False, es' :< EPARAM ref _ k _ _) -> do
>                putEntriesAbove es'
>                ty' <- bquoteHere (pty ref)
>                reactTy <- reactHere (SET :>: ty')
>                d <- hyps bsc me
>                return $ do
>                    d
>                    reactBKind k $ do
>                        fromString $ showRelName $ christenREF bsc ref
>                        reactKword KwAsc
>                        reactTy
>            (True, es' :< EDEF ref _ _ _ _ _) -> do
>                goIn
>                es <- getEntriesAbove
>                (ty :=>: _) <- getGoal "hyps"
>                ty' <- bquoteHere (evTm (inferGoalType es ty))
>                reactTy <- reactHere (SET :>: ty')
>                goOut
>                putEntriesAbove es'
>                d <- hyps bsc me
>                return $ do
>                    d
>                    fromString (showRelName (christenREF bsc ref))
>                    reactKword KwAsc
>                    reactTy
>            (_, es' :< _) -> putEntriesAbove es' >> hyps bsc me

> infoScheme :: RelName -> ProofState PureReact
> infoScheme x = do
>     (_, as, ms) <- resolveHere x
>     case ms of
>         Just sch -> do
>             d <- reactSchemeHere (applyScheme sch as)
>             return d
>         Nothing -> return (fromString (showRelName x ++ " does not have a scheme."))

The `infoWhatIs` command displays a term in various representations.

> infoWhatIs :: DExTmRN -> ProofState PureReact
> infoWhatIs tmd = draftModule "__infoWhatIs" $ do
>     tm :=>: tmv :<: tyv <- elabInfer' tmd
>     tmq <- bquoteHere tmv
>     tms :=>: _ <- distillHere (tyv :>: tmq)
>     ty <- bquoteHere tyv
>     tys :=>: _ <- distillHere (SET :>: ty)
>     return $ Foldable.sequence_
>         [  "Parsed term:", fromString (show tmd)
>         ,  "Elaborated term:", fromString (show tm)
>         ,  "Quoted term:", fromString (show tmq)
>         ,  "Distilled term:", fromString (show tms)
>         ,  "Pretty-printed term:", reactify tms
>         ,  "Inferred type:", fromString (show tyv)
>         ,   "Quoted type:", fromString (show ty)
>         ,   "Distilled type:", fromString (show tys)
>         ,   "Pretty-printed type:", reactify tys
>         ]

Model
=====

A Cochon tactic consists of:

* `ctName` - the name of this tactic
* `ctParse` - parser that parses the arguments for this tactic
* `ctxTrans` - state transition to perform for a given list of arguments and
    current context
* `ctHelp` - help text for this tactic

> data CochonTactic = CochonTactic
>     { ctName   :: String
>     , ctParse  :: Parsley Token (Bwd CochonArg)
>     , ctxTrans :: [CochonArg] -> Cmd ()
>     , ctHelp   :: PureReact
>     }

> instance Show CochonTactic where
>     show = ctName

> instance Eq CochonTactic where
>     ct1 == ct2 =  ctName ct1 == ctName ct2

> instance Ord CochonTactic where
>     compare = comparing ctName

> type InteractionReact = StatefulReact InteractionState ()

> data Pane = Log | Commands | Settings deriving Eq

> data Visibility = Visible | Invisible deriving Eq

> toggleVisibility :: Visibility -> Visibility
> toggleVisibility Visible = Invisible
> toggleVisibility Invisible = Visible

A `Command` is a tactic with arguments and the context it operates on. Also the
resulting output.

> type CTData = (CochonTactic, [CochonArg])

> data Command = Command
>     { commandStr :: String
>     , commandCtx :: (Bwd ProofContext)

Derivative fields - these are less fundamental and can be derived from the
first two fields.

>     , commandParsed :: Either String CTData -- is this really necessary?
>     , commandOutput :: PureReact
>     }

> data ListZip a = ListZip
>     { later  :: Bwd a
>     , focus  :: a
>     , earlier :: Fwd a
>     }

> listZipFromList :: Fwd a -> Maybe (ListZip a)
> listZipFromList (a :> as) = Just (ListZip B0 a as)
> listZipFromList _  = Nothing

> moveEarlier :: ListZip a -> Maybe (ListZip a)
> moveEarlier (ListZip late a (a' :> early)) =
>     Just (ListZip (late :< a) a' early)
> moveEarlier _ = Nothing

> moveLater :: ListZip a -> Maybe (ListZip a)
> moveLater (ListZip (late :< a') a early) =
>     Just (ListZip late a' (a :> early))
> moveLater _ = Nothing

> instance Functor ListZip where
>     fmap f (ListZip late focus early) =
>         ListZip (fmap f late) (f focus) (fmap f early)

> instance Foldable ListZip where
>     foldMap f (ListZip late focus early) =
>         foldMap f late <> f focus <> foldMap f early

we presently need to be able to add a latest, move to earlier / later, and get
the current value

> type InteractionHistory = Fwd Command

> data CommandFocus
>     = InHistory
>         { deferred :: String
>         , current :: (ListZip Command)
>         }
>     | InPresent String

> data InteractionState = InteractionState
>     { _proofCtx :: Bwd ProofContext

There are two fields dealing with the command history.

* `_commandFocus` - the user moves around this by pressing the up and down
  arrows. Up moves back in time and down moves forward in time. Exactly the
  same as your shell command history. When the user reaches a command they like
  and starts to edit it, they're instantly moved forward in time to the
  present.
* `_interactions` - a list of all the things the user has ever typed and
  pigment's responses.

>     , _commandFocus :: CommandFocus
>     , _interactions :: InteractionHistory

Two fields dealing with the right pane (`_currentPane`) is a bit of a misnomer.
It should perhaps be called something like `_currentRightPaneTab` but that's
quite cumbersome.

>     , _rightPaneVisible :: Visibility
>     , _currentPane :: Pane
>     }

> proofCtx :: Lens' InteractionState (Bwd ProofContext)
> proofCtx f state@(InteractionState _proofCtx _ _ _ _) =
>     (\x -> state{_proofCtx=x}) <$> f _proofCtx

> commandFocus :: Lens' InteractionState CommandFocus
> commandFocus f state@(InteractionState _ _commandFocus _ _ _) =
>     (\x -> state{_commandFocus=x}) <$> f _commandFocus

> interactions :: Lens' InteractionState InteractionHistory
> interactions f state@(InteractionState _ _ _interactions _ _) =
>     (\x -> state{_interactions=x}) <$> f _interactions

> rightPaneVisible :: Lens' InteractionState Visibility
> rightPaneVisible f state@(InteractionState _ _ _ _rightPaneVisible _) =
>     (\x -> state{_rightPaneVisible=x}) <$> f _rightPaneVisible

> currentPane :: Lens' InteractionState Pane
> currentPane f state@(InteractionState _ _ _ _ _currentPane) =
>     (\x -> state{_currentPane=x}) <$> f _currentPane

> userInput :: InteractionState -> String
> userInput (InteractionState _ _commandFocus _ _ _) = case _commandFocus of
>     (InHistory _ current) -> let Command str _ _ _ = focus current in str
>     InPresent str -> str

Controller Helpers
==================

TODO(joel) - give this a [CochonArg] reader?

> type Cmd a = WriterT PureReact (State (Bwd ProofContext)) a

> setCtx :: Bwd ProofContext -> Cmd ()
> setCtx = put

> getCtx :: Cmd (Bwd ProofContext)
> getCtx = get

> displayUser :: PureReact -> Cmd ()
> displayUser = tell

> tellUser :: String -> Cmd ()
> tellUser = displayUser . fromString

The `reactBKind` function reactifies a `ParamKind` if supplied with an
element representing its name and type.

> reactBKind :: ParamKind -> PureReact -> PureReact
> reactBKind ParamLam  d = reactKword KwLambda >> d >> reactKword KwArr
> reactBKind ParamAll  d = reactKword KwLambda >> d >> reactKword KwImp
> reactBKind ParamPi   d = "(" >> d >> ")" >> reactKword KwArr

The `reactProofState` command generates a reactified representation of
the proof state at the current location.

> reactProofState :: ProofState PureReact
> reactProofState = do
>     inScope <- getInScope
>     me <- getCurrentName
>     renderReact inScope me

> renderReact :: Entries -> Name -> ProofState PureReact
> renderReact aus me = do
>     es <- replaceEntriesAbove B0
>     cs <- putBelowCursor F0
>     case (es, cs) of
>         (B0, F0) -> reactEmptyTip
>         _ -> do
>             d <- reactEs "" (es <>> F0)
>             d' <- case cs of
>                 F0 -> return d
>                 _ -> do
>                     d'' <- reactEs "" cs
>                     return (d >> "---" >> d'')
>             tip <- reactTip
>             putEntriesAbove es
>             putBelowCursor cs
>             return $ div_ <! class_ "proof-state" $ do
>                 div_ <! class_ "proof-state-inner" $ d'
>                 tip
>     where
>         reactEmptyTip :: ProofState PureReact
>         reactEmptyTip = do
>             tip <- getDevTip
>             case tip of
>                 Module -> return $ div_ <! className "empty-empty-tip" $
>                     "[empty]"
>                 _ -> do
>                     tip' <- reactTip
>                     return $ div_ <! className "empty-tip" $
>                         reactKword KwDefn >> " " >> tip'
>         reactEs :: PureReact
>                 -> Fwd (Entry Bwd)
>                 -> ProofState PureReact
>         reactEs d F0 = return d
>         reactEs d (e :> es) = do
>             putEntryAbove e
>             ed <- reactE e
>             reactEs (d >> ed) es
>         reactE :: Entry Bwd -> ProofState PureReact
>         reactE (EPARAM (_ := DECL :<: ty) (x, _) k _ anchor)  = do
>             ty' <- bquoteHere ty
>             tyd <- reactHereAt (SET :>: ty')
>             return $ reactBKind k $ div_ <! className "entry" $ do
>                 div_ <! class_ "tm-name" $ fromString x
>                 -- TODO(joel) - show anchor in alomst same way as below?
>                 reactKword KwAsc
>                 div_ <! class_ "ty" $ tyd
>         reactE e = do
>             goIn
>             d <- renderReact aus me
>             goOut
>             return $ div_ <! className "entry" $ do
>                 div_ <! class_ "tm-name" $ fromString (fst (entryLastName e))
>                 div_ <! class_ "anchor" $
>                     maybe "" (\x -> "[[" >> fromString x >> "]]") $
>                         entryAnchor e
>                 d

“Developments can be of different nature: this is indicated by the Tip”

> reactTip :: ProofState PureReact
> reactTip = do
>     tip <- getDevTip
>     case tip of
>         Module -> return $ div_ <! className "tip" $ ""
>         Unknown (ty :=>: _) -> do
>             hk <- getHoleKind
>             tyd <- reactHere (SET :>: ty)
>             return $ div_ <! className "tip" $ do
>                 reactHKind hk
>                 reactKword KwAsc
>                 tyd
>         Suspended (ty :=>: _) prob -> do
>             hk <- getHoleKind
>             tyd <- reactHere (SET :>: ty)
>             return $ div_ <! className "tip" $ do
>                 fromString $ "(SUSPENDED: " ++ show prob ++ ")"
>                 reactHKind hk
>                 reactKword KwAsc
>                 tyd
>         Defined tm (ty :=>: tyv) -> do
>             tyd <- reactHere (SET :>: ty)
>             tmd <- reactHereAt (tyv :>: tm)
>             return $ div_ <! className "tip" $
>                 (tmd >> reactKword KwAsc >> tyd)
> reactHKind :: HKind -> PureReact
> reactHKind kind = span_ <! class_ "hole" $ case kind of
>     Waiting    -> "?"
>     Hoping     -> "HOPE?"
>     (Crying s) -> fromString ("CRY <<" ++ s ++ ">>")

The `elm` Cochon tactic elaborates a term, then starts the scheduler to
stabilise the proof state, and returns a pretty-printed representation
of the final type-term pair (using a quick hack).

> elmCT :: DExTmRN -> ProofState PureReact
> elmCT tm = do
>     suspend ("elab" :<: sigSetTM :=>: sigSetVAL) (ElabInferProb tm)
>     startScheduler
>     infoElaborate (DP [("elab", Rel 0)] ::$ [])

View ====

> page :: InteractionReact
> page = div_ <! class_ "page" $ do
>     div_ <! class_ "left-pane" $ do
>         div_ <! class_ "top-pane" $ nest proofCtx proofCtxDisplay
>         div_ <! class_ "bottom-pane" $ do
>             prompt
>             workingOn
>     rightPane

> rightPane :: InteractionReact
> rightPane = do
>     s <- getState
>     when (s^.rightPaneVisible == Visible) innerRightPane
>     paneToggle

> paneToggle :: InteractionReact
> paneToggle = button_ <! class_ "pane-bar"
>                      <! onClick handleToggleRightPane $ do
>     s <- getState
>     let cls = case s^.rightPaneVisible of
>           Invisible -> "icon ion-arrow-left-b"
>           Visible   -> "icon ion-arrow-right-b"
>     i_ <! class_ cls $ ""

> choosePaneButtons :: StatefulReact Pane ()
> choosePaneButtons = div_ <! class_ "choose-pane" $ do
>     pane <- getState
>     let go x = if x == pane then "selected-pane" else ""
>     div_ <! class_ (go Log)
>          <! onClick (handleSelectPane Log) $ "Command Log"
>     div_ <! class_ (go Commands)
>          <! onClick (handleSelectPane Commands) $ "Commands"
>     div_ <! class_ (go Settings)
>          <! onClick (handleSelectPane Settings) $ "Settings"

> innerRightPane :: InteractionReact
> innerRightPane = div_ <! class_ "right-pane" $ do
>     InteractionState{_currentPane=pane} <- getState
>
>     nest currentPane choosePaneButtons
>     case pane of
>         Log -> nest interactions interactionLog
>         Commands -> pureNest tacticList
>         Settings -> "TODO(joel) - settings"

> promptArrow :: StatefulReact a ()
> promptArrow = i_ <! class_ "icon ion-ios-arrow-forward" $ ""

> prompt :: InteractionReact
> prompt = div_ <! class_ "prompt" $ do
>     state <- getState
>     promptArrow
>     input_ <! class_ "prompt-input"
>            <! value_ (toJSStr (userInput state))
>            <! autofocus_ True
>            <! onChange handleCmdChange
>            <! onKeyDown handleKey

> workingOn :: InteractionReact
> workingOn = div_ <! class_ "working-on" $ do
>     InteractionState{_proofCtx=_ :< loc} <- getState
>     let runner = do
>             mty <- optional' getHoleGoal
>             goal <- case mty of
>                 Just (_ :=>: ty) -> showGoal ty
>                 Nothing          -> return ""
>
>             mn <- optional' getCurrentName
>             let name = fromString $ case mn of
>                     Just n   -> showName n
>                     Nothing  -> ""
>
>             return (goal, name)
>
>     pureNest $ case runProofState runner loc of
>         Left err -> err
>         Right ((goal, name), loc') -> goal >> name

> showGoal :: TY -> ProofState PureReact
> showGoal ty@(LABEL _ _) = do
>     h <- infoHypotheses
>     s <- reactHere . (SET :>:) =<< bquoteHere ty
>     return $ div_ <! class_ "goal" $ do
>         h
>         "Programming: "
>         s
> showGoal ty = do
>     s <- reactHere . (SET :>:) =<< bquoteHere ty
>     return $ div_ <! class_ "goal" $ do
>         "Goal: "
>         s

> handleSelectPane :: Pane
>                  -> Pane
>                  -> MouseEvent
>                  -> Pane
> handleSelectPane pane _ _ = pane

> handleToggleRightPane :: InteractionState -> MouseEvent -> InteractionState
> handleToggleRightPane state _ = state & rightPaneVisible %~ toggleVisibility

TODO(joel) - use SpecialKey, etc for state transitions

> data SpecialKey
>     = Enter
>     | UpArrow
>     | DownArrow
>     deriving Show

> handleKey :: InteractionState -> KeyboardEvent -> InteractionState
> handleKey state KeyboardEvent{React.key="Enter"} =
>     runAndLogCmd (userInput state) state
> handleKey state KeyboardEvent{React.key="ArrowUp"} =
>     upArrowTransition state
> handleKey state KeyboardEvent{React.key="ArrowDown"} =
>     downArrowTransition state
> handleKey state a = state

> upArrowTransition :: InteractionState -> InteractionState
> upArrowTransition state = state{_commandFocus=focus'} where
>     hist = _commandFocus state
>     focus' = case hist of
>         (InHistory _ _) -> case moveEarlier (current hist) of
>             Just current' -> hist{current=current'}
>             Nothing -> hist
>         InPresent str -> case listZipFromList (_interactions state) of
>             Just listZip -> InHistory str listZip
>             Nothing -> hist

> downArrowTransition :: InteractionState -> InteractionState
> downArrowTransition state = state{_commandFocus=focus'} where
>     hist = _commandFocus state
>     focus' = case hist of
>         InHistory _ _ -> case moveLater (current hist) of
>             Just current' -> hist{current=current'}
>             Nothing -> InPresent (deferred hist)
>         InPresent str -> hist

> runCmd :: Cmd a -> Bwd ProofContext -> (PureReact, Bwd ProofContext)
> runCmd cmd ctx =
>     let ((_, react), ctx') = runState (runWriterT cmd) ctx
>     in (react, ctx')

> runAndLogCmd :: String
>              -> InteractionState
>              -> InteractionState
> runAndLogCmd cmdStr state =
>     let ctx = state^.proofCtx
>         parsed = parseCmd cmdStr
>         -- XXX parseCmd returns a list in the right side, but we only take
>         -- notice of the first. This is really gross.
>         parsed' = case parsed of
>             Left err -> Left err
>             Right (a:as) -> Right a
>         (output, newCtx) = case parsed' of
>             Left err -> (fromString err, ctx)
>             Right (tac, args) -> runCmd (ctxTrans tac args) ctx
>         cmd' = Command cmdStr ctx parsed' output
>
>     in state & proofCtx .~ newCtx
>              & commandFocus .~ InPresent ""
>              & interactions %~ (cmd' :>)

> handleCmdChange :: InteractionState -> ChangeEvent -> InteractionState
> handleCmdChange state evt =
>     let str = fromJSStr (targetValue evt)
>     in state{_commandFocus=InPresent str}

> interactionLog :: StatefulReact InteractionHistory ()
> interactionLog = div_ <! class_ "interaction-log" $ do
>     logs <- getState
>     pureNest $ Foldable.forM_ logs $ \(Command cmdStr _ _ out) ->
>         div_ <! class_ "log-elem" $ do
>             div_ <! class_ "log-prompt" $ do
>                 promptArrow
>                 " "
>                 fromString cmdStr
>             div_ <! class_ "log-output" $ out

> proofCtxDisplay :: StatefulReact (Bwd ProofContext) ()
> proofCtxDisplay = div_ <! class_ "ctx-display" $ do
>     _ :< ctx <- getState
>     pureNest $ case runProofState reactProofState ctx of
>         Left err -> err
>         Right (display, _) -> display

> tacticList :: PureReact
> tacticList = div_ <! class_ "tactic-list" $
>     Foldable.forM_ cochonTactics $ \tactic ->
>         div_ <! class_ "tactic-info" $ ctHelp tactic

Controller
==========

We start out here. Main calls \`cochon emptyContext\`.

> cochon :: ProofContext -> IO ()
> cochon loc = do
>     Just e <- elemById "inject"
>     let pc = B0 :< loc
>         startState = InteractionState pc (InPresent "") F0 Visible Log
>     validateDevelopment pc
>     render startState e page

TODO refactor / rename this
XXX parseCmd why would ther ever be more than one returned command?

> parseCmd :: String -> Either String [CTData]
> parseCmd l = case parse tokenize l of
>     Left  pf -> Left ("Tokenize failure: " ++ describePFailure pf id)
>     Right ts -> case parse pCochonTactics ts of
>         Left pf -> Left $
>             "Parse failure: " ++
>             describePFailure pf (intercalate " " . map crushToken)
>         Right cds -> Right cds

> paranoid = False
> veryParanoid = False

XXX(joel) refactor this whole thing - remove putStrLn - fix line
length - surely this can be expressed more compactly

> validateDevelopment :: Bwd ProofContext -> IO ()
> validateDevelopment locs@(_ :< loc) = if veryParanoid
>     -- XXX: there must be a better way to do that
>     then Foldable.mapM_ validateCtxt locs
>     else if paranoid
>         then validateCtxt loc
>         else return ()
>   where validateCtxt loc =
>             case evalStateT (validateHere `catchError` catchUnprettyErrors) loc of
>               Left ss -> do
>                   putStrLn "*** Warning: definition failed to type-check! ***"
>                   putStrLn $ renderHouseStyle $ prettyStackError ss
>               _ -> return ()

> describePFailure :: PFailure a -> ([a] -> String) -> String
> describePFailure (PFailure (ts, fail)) f =
>     let errMsg = case fail of
>             Abort        -> "parser aborted."
>             EndOfStream  -> "end of stream."
>             EndOfParser  -> "end of parser."
>             Expect t     -> "expected " ++ f [t] ++ "."
>             Fail s       -> s
>         sucMsg = if length ts > 0
>                then "\nSuccessfully parsed: ``" ++ f ts ++ "''."
>                else ""
>     in errMsg ++ sucMsg

The `tacticsMatching` function identifies Cochon tactics that match the
given string, either exactly or as a prefix.

> tacticsMatching :: String -> [CochonTactic]
> tacticsMatching x = case find ((x ==) . ctName) cochonTactics of
>     Just ct  -> [ct]
>     Nothing  -> filter (isPrefixOf x . ctName) cochonTactics

> tacticNames :: [CochonTactic] -> String
> tacticNames = intercalate ", " . map ctName

Given a proof state command and a context, we can run the command with
|runProofState| to produce a message (either the response from the
command or the error message) and `Maybe` a new proof context.

> runProofState
>     :: ProofState a
>     -> ProofContext
>     -> Either PureReact (a, ProofContext)
> runProofState m loc =
>     case runStateT (m `catchError` catchUnprettyErrors) loc of
>         Right (s, loc') -> Right (s, loc')
>         Left ss         ->
>             Left $ fromString $ renderHouseStyle $ prettyStackError ss

> simpleOutput :: ProofState PureReact -> Cmd ()
> simpleOutput eval = do
>     locs :< loc <- getCtx
>     case runProofState (eval <* startScheduler) loc of
>         Left err -> do
>             setCtx (locs :< loc)
>             displayUser "I'm sorry, Dave. I'm afraid I can't do that."
>             displayUser err
>         Right (msg, loc') -> do
>             setCtx (locs :< loc :< loc')
>             displayUser msg

We have some shortcuts for building common kinds of tactics: |simpleCT|
builds a tactic that works in the proof state, and there are various
specialised versions of it for nullary and unary tactics.

> simpleCT :: String -> Parsley Token (Bwd CochonArg)
>     -> ([CochonArg] -> ProofState PureReact) -> String -> CochonTactic
> simpleCT name parser eval help = CochonTactic
>     {  ctName = name
>     ,  ctParse = parser
>     ,  ctxTrans = simpleOutput . eval
>     ,  ctHelp = fromString help
>     }

> nullaryCT :: String -> ProofState PureReact -> String -> CochonTactic
> nullaryCT name eval help = simpleCT name (pure B0) (const eval) help

> unaryExCT :: String -> (DExTmRN -> ProofState PureReact) -> String -> CochonTactic
> unaryExCT name eval help = simpleCT
>     name
>     (| (B0 :<) tokenExTm
>      | (B0 :<) tokenAscription |)
>     (eval . argToEx . head)
>     help

> unaryInCT :: String -> (DInTmRN -> ProofState PureReact) -> String -> CochonTactic
> unaryInCT name eval help = simpleCT
>     name
>     (| (B0 :<) tokenInTm |)
>     (eval . argToIn . head)
>     help

> unDP :: DExTm p x -> x
> unDP (DP ref ::$ []) = ref

> unaryNameCT :: String -> (RelName -> ProofState PureReact) -> String -> CochonTactic
> unaryNameCT name eval help = simpleCT
>     name
>     (| (B0 :<) tokenName |)
>     (eval . unDP . argToEx . head)
>     help

> unaryStringCT :: String
>               -> (String -> ProofState PureReact)
>               -> String
>               -> CochonTactic
> unaryStringCT name eval help = simpleCT
>     name
>     (| (B0 :<) tokenString |)
>     (eval . argToStr . head)
>     help

The master list of Cochon tactics.

> cochonTactics :: [CochonTactic]
> cochonTactics = sort (

Construction tactics:

>     nullaryCT "apply" (apply >> return "Applied.")
>       "apply - applies the last entry in the development to a new subgoal."
>   : nullaryCT "done" (done >> return "Done.")
>       "done - solves the goal with the last entry in the development."
>   : unaryInCT "give" (\tm -> elabGiveNext tm >> return "Thank you.")
>       "give <term> - solves the goal with <term>."
>   : simpleCT
>         "lambda"
>          (| (|bwdList (pSep (keyword KwComma) tokenString) (%keyword KwAsc%)|) :< tokenInTm
>           | bwdList (pSep (keyword KwComma) tokenString)
>           |)
>          (\ args -> case args of
>             [] -> return "This lambda needs no introduction!"
>             _ -> case last args of
>               InArg ty  -> Data.Traversable.mapM (elabLamParam . (:<: ty) . argToStr) (init args)
>                                >> return "Made lambda!"
>               _         -> Data.Traversable.mapM (lambdaParam . argToStr) args
>                                >> return "Made lambda!"
>            )
>          ("lambda <labels> - introduces one or more hypotheses.\n"++
>           "lambda <labels> : <type> - introduces new module parameters or hypotheses.")
>   : simpleCT
>         "let"
>         (| (| (B0 :< ) tokenString |) :< tokenScheme |)
>         (\ [StrArg x, SchemeArg s] -> do
>             elabLet (x :<: s)
>             optional' problemSimplify
>             optional' seekGoal
>             return (fromString $ "Let there be " ++ x ++ "."))
>         "let <label> <scheme> : <type> - set up a programming problem with a scheme."
>   : simpleCT
>         "make"
>         (| (|(B0 :<) tokenString (%keyword KwAsc%)|) :< tokenInTm
>          | (|(B0 :<) tokenString (%keyword KwDefn%) |) <><
>              (| (\ (tm :<: ty) -> InArg tm :> InArg ty :> F0) pAscription |)
>          |)
>         (\ (StrArg s:tyOrTm) -> case tyOrTm of
>             [InArg ty] -> do
>                 elabMake (s :<: ty)
>                 goIn
>                 return "Appended goal!"
>             [InArg tm, InArg ty] -> do
>                 elabMake (s :<: ty)
>                 goIn
>                 elabGive tm
>                 return "Made."
>         )
>        ("make <x> : <type> - creates a new goal of the given type.\n"
>            ++ "make <x> := <term> - adds a definition to the context.")
>   : unaryStringCT "module" (\s -> makeModule s >> goIn >> return "Made module.")
>       "module <x> - creates a module with name <x>."
>   : simpleCT
>         "pi"
>          (| (|(B0 :<) tokenString (%keyword KwAsc%)|) :< tokenInTm |)
>         (\ [StrArg s, InArg ty] -> elabPiParam (s :<: ty) >> return "Made pi!")
>         "pi <x> : <type> - introduces a pi."
>   : simpleCT
>       "program"
>       (|bwdList (pSep (keyword KwComma) tokenString)|)
>       (\ as -> elabProgram (map argToStr as) >> return "Programming.")
>       "program <labels>: set up a programming problem."
>   : nullaryCT "ungawa" (ungawa >> return "Ungawa!")
>       "ungawa - tries to solve the current goal in a stupid way."

Navigation tactics:

>   : nullaryCT "in" (goIn >> return "Going in...")
>       "in - moves to the bottom-most development within the current one."
>   : nullaryCT "out" (goOutBelow >> return "Going out...")
>       "out - moves to the development containing the current one."
>   : nullaryCT "up" (goUp >> return "Going up...")
>       "up - moves to the development above the current one."
>   : nullaryCT "down" (goDown >> return "Going down...")
>       "down - moves to the development below the current one."
>   : nullaryCT "top" (many' goUp >> return "Going to top...")
>       "top - moves to the top-most development at the current level."
>   : nullaryCT "bottom" (many' goDown >> return "Going to bottom...")
>       "bottom - moves to the bottom-most development at the current level."
>   : nullaryCT "previous" (prevGoal >> return "Going to previous goal...")
>       "previous - searches for the previous goal in the proof state."
>   : nullaryCT "root" (many' goOut >> return "Going to root...")
>       "root - moves to the root of the proof state."
>   : nullaryCT "next" ( nextGoal >> return "Going to next goal...")
>       "next - searches for the next goal in the proof state."
>   : nullaryCT "first"  (some' prevGoal >> return "Going to first goal...")
>       "first - searches for the first goal in the proof state."
>   : nullaryCT "last"   (some' nextGoal >> return "Going to last goal...")
>       "last - searches for the last goal in the proof state."
>   : unaryNameCT "jump" (\ x -> do
>       (n := _) <- resolveDiscard x
>       goTo n
>       return $ fromString $ "Jumping to " ++ showName n ++ "..."
>     )
>       "jump <name> - moves to the definition of <name>."

Miscellaneous tactics:

>     : CochonTactic
>         {  ctName = "undo"
>         ,  ctParse = pure B0
>         ,  ctxTrans = (\_ -> do
>                locs :< loc <- getCtx
>                case locs of
>                    B0  -> tellUser "Cannot undo."  >> setCtx (locs :< loc)
>                    _   -> tellUser "Undone."       >> setCtx locs
>          )
>         ,  ctHelp = fromString "undo - goes back to a previous state."
>         }
>     : nullaryCT "validate" (validateHere >> return "Validated.")
>         "validate - re-checks the definition at the current location."
>   : CochonTactic
>         {  ctName = "data"
>         ,  ctParse = do
>              nom <- tokenString
>              pars <- tokenListArgs (bracket Round $ tokenPairArgs
>                tokenString
>                (keyword KwAsc)
>                tokenInTm) (|()|)
>              keyword KwDefn
>              scs <- tokenListArgs (bracket Round $ tokenPairArgs
>                (|id (%keyword KwTag%)
>                     tokenString |)
>                (keyword KwAsc)
>                tokenInTm)
>               (keyword KwSemi)
>              return $ B0 :< nom :< pars :< scs
>         , ctxTrans = (\[StrArg nom, pars, cons] -> simpleOutput $ do
>               elabData nom (argList (argPair argToStr argToIn) pars)
>                            (argList (argPair argToStr argToIn) cons)
>               return "Data'd.")
>         ,  ctHelp = "data <name> [<para>]* := [(<con> : <ty>) ;]* - builds a data type for thee."
>         }
>   : (simpleCT
>     "eliminate"
>     (|(|(B0 :<) (tokenOption tokenName)|) :< (|id tokenExTm
>                                               |id tokenAscription |)|)
>     (\[n,e] -> elimCTactic (argOption (unDP . argToEx) n) (argToEx e))
>     "eliminate [<comma>] <eliminator> - eliminates with a motive.")
>   : unaryInCT "=" (\tm -> elabGiveNext (DLRET tm) >> return "Ta.")
>       "= <term> - solves the programming problem by returning <term>."
>   : (simpleCT
>      "define"
>      (| (| (B0 :<) tokenExTm |) :< (%keyword KwDefn%) tokenInTm |)
>      (\ [ExArg rl, InArg tm] -> defineCTactic rl tm)
>      "define <prob> := <term> - relabels and solves <prob> with <term>.")

The By gadget, written `\<=`, invokes elimination with a motive, then
simplifies the methods and moves to the first subgoal remaining.

>   : (simpleCT
>     "<="
>     (|(|(B0 :<) (tokenOption tokenName)|) :< (|id tokenExTm
>                                               |id tokenAscription |)|)
>     (\ [n,e] -> byCTactic (argOption (unDP . argToEx) n) (argToEx e))
>     "<= [<comma>] <eliminator> - eliminates with a motive.")

The Refine gadget relabels the programming problem, then either defines
it or eliminates with a motive.

>   : (simpleCT
>     "refine"
>     (|(|(B0 :<) tokenExTm|) :< (|id (%keyword KwEq%) tokenInTm
>                                 |id (%keyword KwBy%) tokenExTm
>                                 |id (%keyword KwBy%) tokenAscription
>                                 |)
>      |)
>     (\ [ExArg rl, arg] -> case arg of
>         InArg tm -> defineCTactic rl tm
>         ExArg tm -> relabel rl >> byCTactic Nothing tm)
>     ("refine <prob> =  <term> - relabels and solves <prob> with <term>.\n" ++
>      "refine <prob> <= <eliminator> - relabels and eliminates with a motive."))
>     : simpleCT
>         "solve"
>         (| (| (B0 :<) tokenName |) :< tokenInTm |)
>         (\ [ExArg (DP rn ::$ []), InArg tm] -> do
>             (ref, spine, _) <- resolveHere rn
>             _ :<: ty <- inferHere (P ref $:$ toSpine spine)
>             _ :=>: tv <- elaborate' (ty :>: tm)
>             tm' <- bquoteHere tv -- force definitional expansion
>             solveHole ref tm'
>             return "Solved."
>           )
>         "solve <name> <term> - solves the hole <name> with <term>."
>   : CochonTactic
>         {  ctName = "idata"
>         ,  ctParse = do
>              nom <- tokenString
>              pars <- tokenListArgs (bracket Round $ tokenPairArgs
>                tokenString
>                (keyword KwAsc)
>                tokenInTm) (|()|)
>              keyword KwAsc
>              indty <- tokenAppInTm
>              keyword KwArr
>              keyword KwSet
>              keyword KwDefn
>              scs <- tokenListArgs (bracket Round $ tokenPairArgs
>                (|id (%keyword KwTag%)
>                     tokenString |)
>                (keyword KwAsc)
>                tokenInTm)
>               (keyword KwSemi)
>              return $ B0 :< nom :< pars :< indty :< scs
>         , ctxTrans = (\ [StrArg nom, pars, indty, cons] -> simpleOutput $
>                     ielabData nom (argList (argPair argToStr argToIn) pars)
>                      (argToIn indty) (argList (argPair argToStr argToIn) cons)
>                       >> return "Data'd.")
>         ,  ctHelp = "idata <name> [<para>]* : <inx> -> Set  := [(<con> : <ty>) ;]* - builds a data type for thee."
>         }
>   : unaryExCT "elm" elmCT "elm <term> - elaborate <term>, stabilise and print type-term pair."
>   : unaryExCT "elaborate" infoElaborate
>       "elaborate <term> - elaborates, evaluates, quotes, distills and pretty-prints <term>."
>   : unaryExCT "infer" infoInfer
>       "infer <term> - elaborates <term> and infers its type."
>   : unaryInCT "parse" (return . fromString . show)
>       "parse <term> - parses <term> and displays the internal display-sytnax representation."
>   : unaryNameCT "scheme" infoScheme
>       "scheme <name> - looks up the scheme on the definition <name>."
>   : unaryStringCT "show" (\s -> case s of
>         "inscope"  -> infoInScope
>         "context"  -> infoContext
>         "dump"     -> infoDump
>         "hyps"     -> infoHypotheses
>         "state"    -> reactProofState
>         _          -> return "show: please specify exactly what to show."
>       )
>       "show <inscope/context/dump/hyps/state> - displays useless information."
>   : unaryExCT "whatis" infoWhatIs
>       "whatis <term> - prints the various representations of <term>."

For testing purposes, we define a @match@ tactic that takes a telescope
of parameters to solve for, a neutral term for which those parameters
are in scope, and another term of the same type. It prints out the
resulting substitution.

>   : (simpleCT
>     "match"
>     (do
>         pars <- tokenListArgs (bracket Round $ tokenPairArgs
>                                       tokenString
>                                       (keyword KwAsc)
>                                       tokenInTm) (| () |)
>         keyword KwSemi
>         tm1 <- tokenExTm
>         keyword KwSemi
>         tm2 <- tokenInTm
>         return (B0 :< pars :< tm1 :< tm2)
>      )
>      (\ [pars, ExArg a, InArg b] ->
>          matchCTactic (argList (argPair argToStr argToIn) pars) a b)
>      "match [<para>]* ; <term> ; <term> - match parameters in first term against second."
>    )
>   : nullaryCT "simplify" (problemSimplify >> optional' seekGoal >> return "Simplified.")
>       "simplify - simplifies the current problem."

TODO(joel) - how did this ever work? pars is not bound here either
https://github.com/joelburget/pigment/blob/bee79687c30933b8199bd9ae6aaaf8048a0c1cf9/src/Tactics/Record.lhs

\< : CochonTactic \< <span> ctName = “record” \< , ctParse = do \< nom
\<- tokenString \< keyword KwDefn \< scs \<- tokenListArgs (bracket
Round \$ tokenPairArgs \< tokenString \< (keyword KwAsc) \< tokenInTm)
\< (keyword KwSemi) \< return \$ B0 :\< nom :\< pars :\< scs \< , ctIO =
( [StrArg nom, pars, cons] -\> simpleOutput \$ \< elabRecord nom
(argList (argPair argToStr argToIn) pars) \< (argList (argPair argToStr
argToIn) cons) \< \>\> return “Record’d.”) \< , ctHelp = “record
\<name\> [\<para\>]\* := [(\<label\> : \<ty\>) ;]\* - builds a record
type.” \< </span>

>   : unaryExCT "relabel" (\ ex -> relabel ex >> return "Relabelled.")
>       "relabel <pattern> - changes names of arguments in label to pattern"
>   : unaryExCT "haskell" (\ t -> elabInfer' t >>= dumpHaskell)
>       "haskell - renders an Epigram term as a Haskell definition."

The `propSimplify` tactic attempts to simplify the type of the current
goal, which should be propositional. Usually one will want to use
|simplify| instead, or simplification will happen automatically (with
the `let` and `\<=` tactics), but this is left for backwards
compatibility.

>   : nullaryCT "propsimplify" propSimplifyTactic
>       "propsimplify - applies propositional simplification to the current goal."
>   : [] )
> elimCTactic :: Maybe RelName -> DExTmRN -> ProofState PureReact
> elimCTactic c r = do
>     c' <- traverse resolveDiscard c
>     (e :=>: _ :<: elimTy) <- elabInferFully r
>     elim c' (elimTy :>: e)
>     toFirstMethod
>     return "Eliminated. Subgoals awaiting work..."
> matchCTactic :: [(String, DInTmRN)]
>              -> DExTmRN
>              -> DInTmRN
>              -> ProofState PureReact
> matchCTactic xs a b = draftModule "__match" $ do
>     rs <- traverse matchHyp xs
>     (_ :=>: av :<: ty) <- elabInfer' a
>     cursorTop
>     (_ :=>: bv) <- elaborate' (ty :>: b)
>     rs' <- runStateT (matchValue B0 (ty :>: (av, bv))) (bwdList rs)
>     return (fromString (show rs'))
>   where
>     matchHyp :: (String, DInTmRN) -> ProofState (REF, Maybe VAL)
>     matchHyp (s, t) = do
>         tt  <- elaborate' (SET :>: t)
>         r   <- assumeParam (s :<: tt)
>         return (r, Nothing)
> propSimplifyTactic :: ProofState PureReact
> propSimplifyTactic = do
>     subs <- propSimplifyHere
>     case subs of
>         B0  -> return "Solved."
>         _   -> do
>             subStrs <- traverse prettyType subs
>             nextGoal
>             return $ fromString ("Simplified to:\n" ++
>                 foldMap (\s -> s ++ "\n") subStrs)
>   where
>     prettyType :: INTM -> ProofState String
>     prettyType ty = prettyHere (SET :>: ty) >>= return . renderHouseStyle

> defineCTactic :: DExTmRN -> DInTmRN -> ProofState PureReact
> defineCTactic rl tm = do
>     relabel rl
>     elabGiveNext (DLRET tm)
>     return "Hurrah!"

> byCTactic :: Maybe RelName -> DExTmRN -> ProofState PureReact
> byCTactic n e = do
>     elimCTactic n e
>     optional' problemSimplify           -- simplify first method
>     many' (goDown >> problemSimplify)   -- simplify other methods
>     many' goUp                          -- go back up to motive
>     optional' seekGoal                  -- jump to goal
>     return "Eliminated and simplified."

> tokenizeCommands :: Parsley Char [String]
> tokenizeCommands = (|id ~ [] (% pEndOfStream %)
>                     |id (% oneLineComment %)
>                         (% consumeUntil' endOfLine %)
>                         tokenizeCommands
>                     |id (% openBlockComment %)
>                         (% (eatNestedComments 0) %)
>                         tokenizeCommands
>                     |id (spaces *> endOfLine *> tokenizeCommands)
>                     |consumeUntil' endOfCommand :
>                      tokenizeCommands
>                     |)
>     where endOfCommand = tokenEq ';' *> spaces *> endOfLine
>                      <|> pEndOfStream *> pure ()
>           endOfLine = tokenEq (head "\n") <|> pEndOfStream
>           oneLineComment = tokenEq '-' *> tokenEq '-'
>           openBlockComment = tokenEq '{' *> tokenEq '-'
>           closeBlockComment = tokenEq '-' *> tokenEq '}'
>           spaces = many $ tokenEq ' '
>           eatNestedComments (-1) = (|id ~ ()|)
>           eatNestedComments i = (|id  (% openBlockComment %)
>                                       (eatNestedComments (i+1))
>                                  |id (% closeBlockComment %)
>                                      (eatNestedComments (i-1))
>                                  |id (% nextToken %)
>                                      (eatNestedComments i) |)

> pCochonTactics :: Parsley Token [CTData]
> pCochonTactics = pSepTerminate (keyword KwSemi) pCochonTactic

> pCochonTactic :: Parsley Token CTData
> pCochonTactic  = do
>     x <- (|id ident
>           |key anyKeyword
>           |)
>     case tacticsMatching x of
>         [ct] -> do
>             args <- ctParse ct
>             return (ct, trail args)
>         [] -> fail "unknown tactic name."
>         cts -> fail $
>             "ambiguous tactic name (could be " ++ tacticNames cts ++ ").")
