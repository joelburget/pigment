{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE OverloadedStrings, GADTs, PatternSynonyms, DataKinds #-}

module Cochon.Tactics (cochonTactics, infoHypotheses, reactBKind, runProofState) where

import Control.Applicative
import Control.Monad
import Control.Monad.Error
import Control.Monad.State
import qualified Data.Foldable as Foldable
import Data.List
import Data.String
import Data.Traversable

import Cochon.CommandLexer
import Cochon.Error
import Cochon.Model
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

import React

cochonTactics :: [CochonTactic]
cochonTactics = sort
    [ applyTac
    , doneTac
    , giveTac
    , lambdaTac
    , letTac
    , makeTac
    , moduleTac
    , piTac
    , programTac
    , ungawaTac
    , inTac
    , outTac
    , upTac
    , downTac
    , topTac
    , bottomTac
    , previousTac
    , rootTac
    , nextTac
    , firstTac
    , lastTac
    , jumpTac
    , undoTac
    , validateTac
    , dataTac
    , eliminateTac
    , retTac
    , defineTac
    , byTac
    , refineTac
    , solveTac
    , idataTac
    , elmTac
    , elaborateTac
    , inferTac
    , parseTac
    , schemeTac
    , showTac
    , whatisTac
    , matchTac
    , simplifyTac
    , relabelTac
    , haskellTac
    ]

{-
We have some shortcuts for building common kinds of tactics: `simpleCT`
builds a tactic that works in the proof state, and there are various
specialised versions of it for nullary and unary tactics.
-}

simpleCT :: String
         -> Parsley Token (Bwd CochonArg)
         -> ([CochonArg] -> ProofState PureReact)
         -> Either PureReact TacticHelp
         -> CochonTactic
simpleCT name parser eval help = CochonTactic
    {  ctName = name
    ,  ctParse = parser
    ,  ctxTrans = simpleOutput . eval
    ,  ctHelp = help
    }

nullaryCT :: String -> ProofState PureReact -> String -> CochonTactic
nullaryCT name eval help =
    simpleCT name (pure B0) (const eval) (Left (fromString help))

unaryExCT :: String -> (DExTmRN -> ProofState PureReact) -> String -> CochonTactic
unaryExCT name eval help = simpleCT
    name
    (| (B0 :<) tokenExTm
     | (B0 :<) tokenAscription |)
    (eval . argToEx . head)
    (Left (fromString help))

unaryInCT :: String -> (DInTmRN -> ProofState PureReact) -> String -> CochonTactic
unaryInCT name eval help = simpleCT
    name
    (| (B0 :<) tokenInTm |)
    (eval . argToIn . head)
    (Left (fromString help))

unDP :: DExTm p x -> x
unDP (DP ref ::$ []) = ref

unaryNameCT :: String -> (RelName -> ProofState PureReact) -> String -> CochonTactic
unaryNameCT name eval help = simpleCT
    name
    (| (B0 :<) tokenName |)
    (eval . unDP . argToEx . head)
    (Left (fromString help))

unaryStringCT :: String
              -> (String -> ProofState PureReact)
              -> String
              -> CochonTactic
unaryStringCT name eval help = simpleCT
    name
    (| (B0 :<) tokenString |)
    (eval . argToStr . head)
    (Left (fromString help))


-- Construction Tactics

applyTac = nullaryCT "apply" (apply >> return "Applied.")
  "apply - applies the last entry in the development to a new subgoal."

doneTac = nullaryCT "done" (done >> return "Done.")
  "done - solves the goal with the last entry in the development."

giveTac = unaryInCT "give" (\tm -> elabGiveNext tm >> return "Thank you.")
  "give <term> - solves the goal with <term>."

-- TODO(joel) - rename lambda

lambdaTac = simpleCT
    "lambda"
     (| (|bwdList (pSep (keyword KwComma) tokenString) (%keyword KwAsc%)|) :< tokenInTm
      | bwdList (pSep (keyword KwComma) tokenString)
      |)
     (\ args -> case args of
        [] -> return "This lambda needs no introduction!"
        _ -> case last args of
          InArg ty  -> Data.Traversable.mapM (elabLamParam . (:<: ty) . argToStr) (init args)
                           >> return "Made lambda!"
          _         -> Data.Traversable.mapM (lambdaParam . argToStr) args
                           >> return "Made lambda!"
       )
     (Right (TacticHelp
         "lambda <labels> [ : <type> ]"
         "lambda X, Y : Set"
         -- TODO(joel) - better description
         "introduce new module parameters or hypotheses"
         [ ("<labels>", "One or more names to introduce")
         , ("<type>", "(optional) their type")
         ]
     ))

letTac = simpleCT
    "let"
    (| (| (B0 :< ) tokenString |) :< tokenScheme |)
    (\ [StrArg x, SchemeArg s] -> do
        elabLet (x :<: s)
        optional' problemSimplify
        optional' seekGoal
        return (fromString $ "Let there be " ++ x ++ "."))
    (Right (TacticHelp
        "let <label> <scheme> : <type>"
        "let A (m : Nat) : Nat -> Nat"
        -- TODO(joel) - better description
        "introduce new module parameters or hypotheses"
        [ ("<labels>", "One or more names to introduce")
        , ("<type>", "(optional) their type")
        ]
    ))

makeTac = simpleCT
    "make"
    (| (|(B0 :<) tokenString (%keyword KwAsc%)|) :< tokenInTm
     | (|(B0 :<) tokenString (%keyword KwDefn%) |) <><
         (| (\ (tm :<: ty) -> InArg tm :> InArg ty :> F0) pAscription |)
     |)
    (\ (StrArg s:tyOrTm) -> case tyOrTm of
        [InArg ty] -> do
            elabMake (s :<: ty)
            goIn
            return "Appended goal!"
        [InArg tm, InArg ty] -> do
            elabMake (s :<: ty)
            goIn
            elabGive tm
            return "Made."
    )
    (Right (TacticHelp
        "make <x> : <type> OR make <x> := <term> : <type>"
        "make A := ? : Set"
        -- TODO(joel) - better description
        "the first form creates a new goal of the given type; the second adds a definition to the context"
        [ ("<x>", "New name to introduce")
        , ("<term>", "its definition (this could be a hole (\"?\"))")
        , ("<type>", "its type (this could be a hole (\"?\"))")
        ]
    ))

moduleTac = unaryStringCT "module"
    (\s -> makeModule DevelopModule s >> goIn >> return "Made module.")
    "module <x> - creates a module with name <x>."

piTac = simpleCT
    "pi"
     (| (|(B0 :<) tokenString (%keyword KwAsc%)|) :< tokenInTm |)
    (\ [StrArg s, InArg ty] -> elabPiParam (s :<: ty) >> return "Made pi!")
    (Right (TacticHelp
        "pi <x> : <type>"
        "pi A : Set"
        -- TODO(joel) - better description
        "introduce a pi (what's a pi?)"
        [ ("<x>", "Pi to introduce")
        , ("<type>", "its type")
        ]
    ))

programTac = simpleCT
    "program"
    (|bwdList (pSep (keyword KwComma) tokenString)|)
    (\ as -> elabProgram (map argToStr as) >> return "Programming.")
    (Right (TacticHelp
        "program <labels>"
        "(make plus : Nat -> Nat -> Nat) ; program x, y ;"
        -- TODO(joel) - better description
        "set up a programming problem"
        [ ("<labels>", "One or more names to introduce")
        ]
    ))

ungawaTac = nullaryCT "ungawa" (ungawa >> return "Ungawa!")
    "ungawa - tries to solve the current goal in a stupid way."


-- Navigation Tactics

inTac = nullaryCT "in" (goIn >> return "Going in...")
    "in - moves to the bottom-most development within the current one."

outTac = nullaryCT "out" (goOutBelow >> return "Going out...")
    "out - moves to the development containing the current one."

upTac = nullaryCT "up" (goUp >> return "Going up...")
    "up - moves to the development above the current one."

downTac = nullaryCT "down" (goDown >> return "Going down...")
    "down - moves to the development below the current one."

topTac = nullaryCT "top" (many' goUp >> return "Going to top...")
    "top - moves to the top-most development at the current level."

bottomTac = nullaryCT "bottom" (many' goDown >> return "Going to bottom...")
    "bottom - moves to the bottom-most development at the current level."

previousTac = nullaryCT "previous" (prevGoal >> return "Going to previous goal...")
    "previous - searches for the previous goal in the proof state."

rootTac = nullaryCT "root" (many' goOut >> return "Going to root...")
    "root - moves to the root of the proof state."

nextTac = nullaryCT "next" ( nextGoal >> return "Going to next goal...")
    "next - searches for the next goal in the proof state."

firstTac = nullaryCT "first"  (some' prevGoal >> return "Going to first goal...")
    "first - searches for the first goal in the proof state."

lastTac = nullaryCT "last"   (some' nextGoal >> return "Going to last goal...")
    "last - searches for the last goal in the proof state."

jumpTac = unaryNameCT "jump" (\ x -> do
    (n := _) <- resolveDiscard x
    goTo n
    return $ fromString $ "Jumping to " ++ showName n ++ "..."
  )
    "jump <name> - moves to the definition of <name>."


-- Miscellaneous tactics

-- TODO visual display of previous states
undoTac = CochonTactic
    {  ctName = "undo"
    ,  ctParse = pure B0
    ,  ctxTrans = (\_ -> do
           locs :< loc <- getCtx
           case locs of
               B0  -> tellUser "Cannot undo."  >> setCtx (locs :< loc)
               _   -> tellUser "Undone."       >> setCtx locs
     )
    ,  ctHelp = Right (TacticHelp
           "undo"
           "undo"
           "goes back to a previous state."
           []
       )
    }

validateTac = nullaryCT "validate" (validateHere >> return "Validated.")
    "validate - re-checks the definition at the current location."

dataTac = CochonTactic
    {  ctName = "data"
    ,  ctParse = do
         nom <- tokenString
         pars <- tokenListArgs (bracket Round $ tokenPairArgs
           tokenString
           (keyword KwAsc)
           tokenInTm) (pure ())
         keyword KwDefn
         scs <- tokenListArgs
             (bracket Round $ tokenPairArgs
                 (keyword KwTag >> tokenString)
                 (keyword KwAsc)
                 tokenInTm
             )
             (keyword KwSemi)
         return $ B0 :< nom :< pars :< scs
    , ctxTrans = (\[StrArg nom, pars, cons] -> simpleOutput $ do
          elabData nom (argList (argPair argToStr argToIn) pars)
                       (argList (argPair argToStr argToIn) cons)
          return "Data'd.")
    ,  ctHelp = Right (TacticHelp
           "data <name> [<para>]* := [(<con> : <ty>) ;]*"
           "data List (X : Set) := ('nil : List X) ; ('cons : X -> List X -> List X) ;"
           "Create a new data type"
           [ ("<name>", "Choose the name of your datatype carefully")
           , ("<para>", "Type parameters")
           , ("<con : ty>", "Give each constructor a unique name and a type")
           ]
       )
    }

eliminateTac = simpleCT
    "eliminate"
    (|(|(B0 :<) (tokenOption tokenName)|) :< (|id tokenExTm
                                              |id tokenAscription |)|)
    (\[n,e] -> elimCTactic (argOption (unDP . argToEx) n) (argToEx e))
    (Right (TacticHelp
        "eliminate [<comma>] <eliminator>"
        "eliminate induction NatD m"
        -- TODO(joel) - better description
        "eliminate with a motive (same as <=)"
        [ ("<comma>", "TODO(joel)")
        , ("<eliminator>", "TODO(joel)")
        ]
    ))

retTac = unaryInCT "=" (\tm -> elabGiveNext (DLRET tm) >> return "Ta.")
    "= <term> - solves the programming problem by returning <term>."

defineTac = simpleCT
     "define"
     (| (| (B0 :<) tokenExTm |) :< (%keyword KwDefn%) tokenInTm |)
     (\ [ExArg rl, InArg tm] -> defineCTactic rl tm)
    (Right (TacticHelp
        "define <prob> := <term>"
        "define vappend 'zero 'nil k bs := bs"
        -- TODO(joel) - better description
        "relabel and solve <prob> with <term>"
        [ ("<prob>", "pattern to match and define")
        , ("<term>", "solution to the problem")
        ]
    ))

-- The By gadget, written `<=`, invokes elimination with a motive, then
-- simplifies the methods and moves to the first subgoal remaining.

byTac = simpleCT
    "<="
    (|(|(B0 :<) (tokenOption tokenName)|) :< (|id tokenExTm
                                              |id tokenAscription |)|)
    (\ [n,e] -> byCTactic (argOption (unDP . argToEx) n) (argToEx e))
    (Right (TacticHelp
        "<= [<comma>] <eliminator>"
        "<= induction NatD m"
        -- TODO(joel) - better description
        "eliminate with a motive (same as eliminate)"
        [ ("<comma>", "TODO(joel)")
        , ("<eliminator>", "TODO(joel)")
        ]
    ))

-- The Refine gadget relabels the programming problem, then either defines
-- it or eliminates with a motive.

refineTac = simpleCT
    "refine"
    (|(|(B0 :<) tokenExTm|) :< (|id (%keyword KwEq%) tokenInTm
                                |id (%keyword KwBy%) tokenExTm
                                |id (%keyword KwBy%) tokenAscription
                                |)
     |)
    (\ [ExArg rl, arg] -> case arg of
        InArg tm -> defineCTactic rl tm
        ExArg tm -> relabel rl >> byCTactic Nothing tm)
    (Right (TacticHelp
        "refine <prob> = <term> OR refine <prob> <= <eliminator>"
        "refine plus 'zero n = n"
        -- TODO(joel) - better description
        "relabel and solve or eliminate with a motive"
        [ ("<prob>", "TODO(joel)")
        , ("<term>", "TODO(joel)")
        , ("<prob>", "TODO(joel)")
        , ("<eliminator>", "TODO(joel)")
        ]
    ))

solveTac = simpleCT
    "solve"
    (| (| (B0 :<) tokenName |) :< tokenInTm |)
    (\ [ExArg (DP rn ::$ []), InArg tm] -> do
        (ref, spine, _) <- resolveHere rn
        _ :<: ty <- inferHere (P ref $:$ toSpine spine)
        _ :=>: tv <- elaborate' (ty :>: tm)
        tm' <- bquoteHere tv -- force definitional expansion
        solveHole ref tm'
        return "Solved."
      )
    (Right (TacticHelp
        "solve <name> <term>"
        "solve a hole"
        -- TODO(joel) - better description
        "make A := ? : Set; solve A Set"
        [ ("<name>", "The name of the hole to solve")
        , ("<term>", "Its solution")
        ]
    ))

idataTac = CochonTactic
    {  ctName = "idata"
    ,  ctParse = do
         nom <- tokenString
         pars <- tokenListArgs (bracket Round $ tokenPairArgs
           tokenString
           (keyword KwAsc)
           tokenInTm) (|()|)
         keyword KwAsc
         indty <- tokenAppInTm
         keyword KwArr
         keyword KwSet
         keyword KwDefn
         scs <- tokenListArgs (bracket Round $ tokenPairArgs
           (|id (%keyword KwTag%)
                tokenString |)
           (keyword KwAsc)
           tokenInTm)
          (keyword KwSemi)
         return $ B0 :< nom :< pars :< indty :< scs
    , ctxTrans = (\ [StrArg nom, pars, indty, cons] -> simpleOutput $
                ielabData nom (argList (argPair argToStr argToIn) pars)
                 (argToIn indty) (argList (argPair argToStr argToIn) cons)
                  >> return "Data'd.")
    , ctHelp = Right (TacticHelp
           "idata <name> [<para>]* : <inx> -> Set  := [(<con> : <ty>) ;]*"
           "idata Vec (A : Set) : Nat -> Set := ('cons : (n : Nat) -> (a : A) -> (as : Vec A n) -> Vec A ('suc n)) ;"
           "Create a new indexed data type"
           [ ("<name>", "Choose the name of your datatype carefully")
           , ("<para>", "Type parameters")
           , ("<inx>", "??")
           , ("<con : ty>", "Give each constructor a unique name and a type")
           ]
       )
    }

{-
The `elm` Cochon tactic elaborates a term, then starts the scheduler to
stabilise the proof state, and returns a pretty-printed representation
of the final type-term pair (using a quick hack).
-}

elmCT :: DExTmRN -> ProofState PureReact
elmCT tm = do
    suspend ("elab" :<: sigSetTM :=>: sigSetVAL) (ElabInferProb tm)
    startScheduler
    infoElaborate (DP [("elab", Rel 0)] ::$ [])

elmTac = unaryExCT "elm" elmCT "elm <term> - elaborate <term>, stabilise and print type-term pair."

elaborateTac = unaryExCT "elaborate" infoElaborate
  "elaborate <term> - elaborates, evaluates, quotes, distills and pretty-prints <term>."

inferTac = unaryExCT "infer" infoInfer
  "infer <term> - elaborates <term> and infers its type."

parseTac = unaryInCT "parse" (return . fromString . show)
  "parse <term> - parses <term> and displays the internal display-sytnax representation."

schemeTac = unaryNameCT "scheme" infoScheme
  "scheme <name> - looks up the scheme on the definition <name>."

showTac = unaryStringCT "show" (\s -> case s of
    "inscope"  -> infoInScope
    "context"  -> infoContext
    "dump"     -> infoDump
    "hyps"     -> infoHypotheses
    -- "state"    -> reactProofState
    _          -> return "show: please specify exactly what to show."
  )
  "show <inscope/context/dump/hyps/state> - displays useless information."

whatisTac = unaryExCT "whatis" infoWhatIs
  "whatis <term> - prints the various representations of <term>."

{-
For testing purposes, we define a @match@ tactic that takes a telescope
of parameters to solve for, a neutral term for which those parameters
are in scope, and another term of the same type. It prints out the
resulting substitution.
-}

matchTac = simpleCT
    "match"
    (do
        pars <- tokenListArgs (bracket Round $ tokenPairArgs
                                      tokenString
                                      (keyword KwAsc)
                                      tokenInTm) (| () |)
        keyword KwSemi
        tm1 <- tokenExTm
        keyword KwSemi
        tm2 <- tokenInTm
        return (B0 :< pars :< tm1 :< tm2)
     )
     (\ [pars, ExArg a, InArg b] ->
         matchCTactic (argList (argPair argToStr argToIn) pars) a b)
    (Right (TacticHelp
        "match [<para>]* ; <term> ; <term>"
        "TODO(joel)"
        -- TODO(joel) - better description
        "match parameters in first term against second."
        [ ("<para>", "TODO(joel)")
        , ("<term>", "TODO(joel)")
        ]
    ))

simplifyTac = nullaryCT "simplify" (problemSimplify >> optional' seekGoal >> return "Simplified.")
    "simplify - simplifies the current problem."

{-
TODO(joel) - how did this ever work? pars is not bound here either
https://github.com/joelburget/pigment/blob/bee79687c30933b8199bd9ae6aaaf8048a0c1cf9/src/Tactics/Record.lhs

recordTac = CochonTactic
    {  ctName = "record"
    ,  ctParse = do
         nom <- tokenString
         keyword KwDefn
         scs <- tokenListArgs (bracket Round $ tokenPairArgs
           tokenString
           (keyword KwAsc)
           tokenInTm)
          (keyword KwSemi)
         return $ B0 :< nom :< pars :< scs
    , ctIO = (\ [StrArg nom, pars, cons] -> simpleOutput $
                elabRecord nom (argList (argPair argToStr argToIn) pars)
                               (argList (argPair argToStr argToIn) cons)
                  >> return "Record'd.")
    ,  ctHelp = "record <name> [<para>]* := [(<label> : <ty>) ;]* - builds a record type."
    }
-}

relabelTac = unaryExCT "relabel" (\ ex -> relabel ex >> return "Relabelled.")
    "relabel <pattern> - changes names of arguments in label to pattern"

haskellTac = unaryExCT "haskell" (\ t -> elabInfer' t >>= dumpHaskell)
    "haskell - renders an Epigram term as a Haskell definition."

-- end tactics, begin a bunch of weird "info" stuff and other helpers


-- The `propSimplify` tactic attempts to simplify the type of the current
-- goal, which should be propositional. Usually one will want to use
-- |simplify| instead, or simplification will happen automatically (with
-- the `let` and `<=` tactics), but this is left for backwards
-- compatibility.
--
-- propsimplifyTac = nullaryCT "propsimplify" propSimplifyTactic
--     "propsimplify - applies propositional simplification to the current goal."

propSimplifyTactic :: ProofState PureReact
propSimplifyTactic = do
    subs <- propSimplifyHere
    case subs of
        B0  -> return "Solved."
        _   -> do
            subStrs <- traverse prettyType subs
            nextGoal
            return $ fromString ("Simplified to:\n" ++
                Foldable.foldMap (\s -> s ++ "\n") subStrs)
  where
    prettyType :: INTM -> ProofState String
    prettyType ty = prettyHere (SET :>: ty) >>= return . renderHouseStyle

infoInScope :: ProofState PureReact
infoInScope = do
    pc <- get
    inScope <- getInScope
    return (fromString (showEntries (inBScope pc) inScope))

infoDump :: ProofState PureReact
infoDump = gets (fromString . show)

-- The `infoElaborate` command calls `elabInfer` on the given neutral
-- display term, evaluates the resulting term, bquotes it and returns a
-- pretty-printed string representation. Note that it works in its own
-- module which it discards at the end, so it will not leave any subgoals
-- lying around in the proof state.

infoElaborate :: DExTmRN -> ProofState PureReact
infoElaborate tm = draftModule "__infoElaborate" $ do
    (tm' :=>: tmv :<: ty) <- elabInfer' tm
    tm'' <- bquoteHere tmv
    s <- reactHere (ty :>: tm'')
    return s

-- The `infoInfer` command is similar to `infoElaborate`, but it returns a
-- string representation of the resulting type.

infoInfer :: DExTmRN -> ProofState PureReact
infoInfer tm = draftModule "__infoInfer" $ do
    (_ :<: ty) <- elabInfer' tm
    ty' <- bquoteHere ty
    s <- reactHere (SET :>: ty')
    return s

-- The `infoContextual` command displays a distilled list of things in the
-- context, parameters if the argument is False or definitions if the
-- argument is True.

infoHypotheses  = infoContextual False
infoContext     = infoContextual True

infoContextual :: Bool -> ProofState PureReact
infoContextual gals = do
    inScope <- getInScope
    bsc <- gets inBScope
    d <- help bsc inScope
    return d
  where
    help :: BScopeContext -> Entries -> ProofState PureReact
    help bsc B0 = return ""
    help bsc (es :< EPARAM ref _ k _ _ _) | not gals = do
        ty       <- bquoteHere (pty ref)
        reactTy  <- reactHereAt (SET :>: ty)
        d        <- help bsc es
        return $ do
            d
            reactBKind k $ do
                fromString $ showRelName $ christenREF bsc ref
                reactKword KwAsc
                reactTy
    help bsc (es :< EDEF ref _ _ _ _ _ _) | gals = do
        ty       <- bquoteHere $ removeShared (paramSpine es) (pty ref)
        reactTy  <- reactHere (SET :>: ty)
        d        <- help bsc es
        return $ do
            d
            fromString $ showRelName $ christenREF bsc ref
            reactKword KwAsc
            reactTy
    help bsc (es :< _) = help bsc es
    removeShared :: Spine TT REF -> TY -> TY
    removeShared []       ty        = ty
    removeShared (A (NP r) : as) (PI s t)  = t Evidences.Eval.$$ A (NP r)

-- This old implementation is written using a horrible imperative hack that
-- saves the state, throws away bits of the context to produce an answer,
-- then restores the saved state. We can get rid of it once we are
-- confident that the new version (above) produces suitable output.

infoContextual' :: Bool -> ProofState PureReact
infoContextual' gals = do
    save <- get
    let bsc = inBScope save
    me <- getCurrentName
    ds <- many' (hypsHere bsc me <* optional' killBelow <* goOut <* removeEntryAbove)
    d <- hypsHere bsc me
    put save
    return $ sequence_ $ d:reverse ds
 where
   hypsHere :: BScopeContext -> Name -> ProofState PureReact
   hypsHere bsc me = do
       es <- getEntriesAbove
       d <- hyps bsc me
       putEntriesAbove es
       return d
   killBelow = do
       l <- getLayer
       replaceLayer (l { belowEntries = NF F0 })
   hyps :: BScopeContext -> Name -> ProofState PureReact
   hyps bsc me = do
       es <- getEntriesAbove
       case (gals, es) of
           (_, B0) -> return ""
           (False, es' :< EPARAM ref _ k _ _ _) -> do
               putEntriesAbove es'
               ty' <- bquoteHere (pty ref)
               reactTy <- reactHere (SET :>: ty')
               d <- hyps bsc me
               return $ do
                   d
                   reactBKind k $ do
                       fromString $ showRelName $ christenREF bsc ref
                       reactKword KwAsc
                       reactTy
           (True, es' :< EDEF ref _ _ _ _ _ _) -> do
               goIn
               es <- getEntriesAbove
               (ty :=>: _) <- getGoal "hyps"
               ty' <- bquoteHere (evTm (inferGoalType es ty))
               reactTy <- reactHere (SET :>: ty')
               goOut
               putEntriesAbove es'
               d <- hyps bsc me
               return $ do
                   d
                   fromString (showRelName (christenREF bsc ref))
                   reactKword KwAsc
                   reactTy
           (_, es' :< _) -> putEntriesAbove es' >> hyps bsc me

infoScheme :: RelName -> ProofState PureReact
infoScheme x = do
    (_, as, ms) <- resolveHere x
    case ms of
        Just sch -> do
            d <- reactSchemeHere (applyScheme sch as)
            return d
        Nothing -> return (fromString (showRelName x ++ " does not have a scheme."))

-- The `infoWhatIs` command displays a term in various representations.

infoWhatIs :: DExTmRN -> ProofState PureReact
infoWhatIs tmd = draftModule "__infoWhatIs" $ do
    tm :=>: tmv :<: tyv <- elabInfer' tmd
    tmq <- bquoteHere tmv
    tms :=>: _ <- distillHere (tyv :>: tmq)
    ty <- bquoteHere tyv
    tys :=>: _ <- distillHere (SET :>: ty)
    return $ sequence_
        [  "Parsed term:", fromString (show tmd)
        ,  "Elaborated term:", fromString (show tm)
        ,  "Quoted term:", fromString (show tmq)
        ,  "Distilled term:", fromString (show tms)
        ,  "Pretty-printed term:", reactify tms
        ,  "Inferred type:", fromString (show tyv)
        ,   "Quoted type:", fromString (show ty)
        ,   "Distilled type:", fromString (show tys)
        ,   "Pretty-printed type:", reactify tys
        ]

byCTactic :: Maybe RelName -> DExTmRN -> ProofState PureReact
byCTactic n e = do
    elimCTactic n e
    optional' problemSimplify           -- simplify first method
    many' (goDown >> problemSimplify)   -- simplify other methods
    many' goUp                          -- go back up to motive
    optional' seekGoal                  -- jump to goal
    return "Eliminated and simplified."

defineCTactic :: DExTmRN -> DInTmRN -> ProofState PureReact
defineCTactic rl tm = do
    relabel rl
    elabGiveNext (DLRET tm)
    return "Hurrah!"

matchCTactic :: [(String, DInTmRN)]
             -> DExTmRN
             -> DInTmRN
             -> ProofState PureReact
matchCTactic xs a b = draftModule "__match" $ do
    rs <- traverse matchHyp xs
    (_ :=>: av :<: ty) <- elabInfer' a
    cursorTop
    (_ :=>: bv) <- elaborate' (ty :>: b)
    rs' <- runStateT (matchValue B0 (ty :>: (av, bv))) (bwdList rs)
    return (fromString (show rs'))
  where
    matchHyp :: (String, DInTmRN) -> ProofState (REF, Maybe VAL)
    matchHyp (s, t) = do
        tt  <- elaborate' (SET :>: t)
        r   <- assumeParam (s :<: tt)
        return (r, Nothing)

elimCTactic :: Maybe RelName -> DExTmRN -> ProofState PureReact
elimCTactic c r = do
    c' <- traverse resolveDiscard c
    (e :=>: _ :<: elimTy) <- elabInferFully r
    elim c' (elimTy :>: e)
    toFirstMethod
    return "Eliminated. Subgoals awaiting work..."

simpleOutput :: ProofState PureReact -> Cmd ()
simpleOutput eval = do
    locs :< loc <- getCtx
    case runProofState (eval <* startScheduler) loc of
        Left err -> do
            setCtx (locs :< loc)
            displayUser "I'm sorry, Dave. I'm afraid I can't do that."
            displayUser err
        Right (msg, loc') -> do
            setCtx (locs :< loc :< loc')
            displayUser msg

-- The `reactBKind` function reactifies a `ParamKind` if supplied with an
-- element representing its name and type.

reactBKind :: ParamKind -> React a () -> React a ()
reactBKind ParamLam  d = reactKword KwLambda >> d >> reactKword KwArr
reactBKind ParamAll  d = reactKword KwLambda >> d >> reactKword KwImp
reactBKind ParamPi   d = "(" >> d >> ")" >> reactKword KwArr

-- Given a proof state command and a context, we can run the command with
-- `runProofState` to produce a message (either the response from the
-- command or the error message) and `Maybe` a new proof context.

runProofState
    :: ProofState a
    -> ProofContext
    -> Either PureReact (a, ProofContext)
runProofState m loc =
    case runStateT (m `catchError` catchUnprettyErrors) loc of
        Right (s, loc') -> Right (s, loc')
        Left ss         ->
            Left $ fromString $ renderHouseStyle $ prettyStackError ss
