{-# LANGUAGE OverloadedStrings, GADTs, PatternSynonyms, DataKinds,
  LambdaCase, LiberalTypeSynonyms, MultiParamTypeClasses, DeriveGeneric #-}

module Cochon.Tactics where

import Control.Applicative hiding (empty)
import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Foldable as Foldable
import GHC.Generics
import Data.List
import Data.Monoid
import Data.Ord
import Data.String
import Data.Traversable as Trav
import qualified Data.Text as T
import Data.Text (Text)
import Text.PrettyPrint.HughesPJ hiding ((<>))

import Control.Error
import Data.Void

import Cochon.CommandLexer
import Cochon.Model (runProofState)
import Cochon.PrettyProofState
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
import Evidences.DefinitionalEquality
import Evidences.Eval hiding (($$))
import qualified Evidences.Eval (($$))
import Evidences.Tm
import Kit.BwdFwd
import Kit.ListZip
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


tellTermHere :: (TY :>: INTM) -> ProofState String
tellTermHere tt = renderHouseStyle <$> prettyHere tt


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
    -- , idataTac
    , elmTac
    , elaborateTac
    -- TODO(joel) - figure out a system for synonyms
    , elabTac
    , inferTac
    , parseTac
    -- , schemeTac
    , dumpTac
    , whatisTac
    , matchTac
    , simplifyTac
    , relabelTac
    , doitTac
    , autoTac
    ]


{-
We have some shortcuts for building common kinds of tactics: `simpleCT`
builds a tactic that works in the proof state, and there are various
specialised versions of it for nullary and unary tactics.
-}
simpleCT :: Text
         -> Historic
         -> Text
         -> TacticDescription
         -> (TacticResult -> ProofState String)
         -> TacticHelp
         -> CochonTactic
simpleCT name hist desc fmt eval help = CochonTactic
    {  ctName = name
    ,  ctMessage = desc
    ,  ctDesc = fmt
    ,  ctxTrans = simpleOutput hist . eval
    ,  ctHelp = help
    }


nullaryCT :: Text
          -> Historic
          -> ProofState String
          -> Text
          -> CochonTactic
nullaryCT name hist eval desc = simpleCT
    name
    hist
    desc
    (TfInlineSequence [])
    (const eval)
    (TacticHelp
        (name <> " - " <> desc)
        "" "" []
    )


unaryExCT :: Text
          -> (DExTmRN -> ProofState String)
          -> Text
          -> CochonTactic
unaryExCT name eval help = simpleCT
    name
    Historic
    help
    (TfBlockSequence
        [ TfExArg "term" Nothing
        , TfAlternative
            ( TfExArg "term" Nothing
            , TfInlineSequence
                [ TfInArg "term" Nothing
                , TfKeyword KwAsc
                , TfInArg "ty" Nothing
                ]
            )
        ]
    )
    (eval . argToEx)
    (TacticHelp help "" "" [])


unaryInCT :: Text
          -> (DInTmRN -> ProofState String)
          -> Text
          -> CochonTactic
unaryInCT name eval desc = simpleCT
    name
    Historic
    desc
    (TfInlineSequence [ TfInArg "term" Nothing ])
    (eval . argToIn)
    (TacticHelp (name <> " - " <> desc) "" "" [])


unDP :: DExTm p x -> x
unDP (DP ref ::$ []) = ref


unaryNameCT :: Text
            -> (RelName -> ProofState String)
            -> Text
            -> CochonTactic
unaryNameCT name eval desc = simpleCT
    name
    Historic
    desc
    (TfInlineSequence [ TfName "name" ])
    (eval . unDP . argToEx)
    (TacticHelp (name <> " - " <> desc) "" "" [])


unaryStringCT :: Text
              -> (Text -> ProofState String)
              -> Text
              -> CochonTactic
unaryStringCT name eval desc = simpleCT
    name
    Historic
    desc
    (TfInlineSequence [ TfName "x" ])
    (eval . argToStr)
    (TacticHelp (name <> " - " <> desc) "" "" [])


-- Construction Tactics
applyTac = nullaryCT "apply" Historic (apply >> return "Applied.")
  "applies the last entry in the development to a new subgoal."


doneTac = nullaryCT "done" Historic (done >> return "Done.")
  "solves the goal with the last entry in the development."


-- retTac = unaryInCT "=" (\tm -> elabGiveNext (DLRET tm) >> return "Solved.")
giveTac = unaryInCT "give" (\tm -> elabGiveNext tm >> return "Thank you.")
  "solves the goal with <term>."


-- TODO(joel) - rename lambda, understand difference between let and lambda
lambdaTac = simpleCT
    "lambda"
    Historic
    "introduce new module parameters or hypotheses"
     (TfBlockSequence
         [ TfSep (TfName "label") KwComma
         , TfOption (
                TfInlineSequence
                    [ TfKeyword KwAsc
                    , TfInArg "type" (Just "(optional) their type")
                    ]
           )
         ]
     )
     (\case
          -- TODO(joel) - give an actually useful message
          TrSequence [ TrSequence [], _ ] ->
              return "This lambda needs no introduction!"
          TrSequence [ TrSequence args, TrOption (Just (TrInArg ty)) ] -> do
              Trav.mapM (elabLamParam . (:<: ty) . T.unpack . argToStr) args
              return "Lambdafied"
          TrSequence [ TrSequence args, TrOption (Nothing) ] -> do
              Trav.mapM (lambdaParam . T.unpack . argToStr) args
              return "Lambdafied"
       )
     (TacticHelp
         "lambda <labels> [ : <type> ]"
         "lambda X, Y : Set"
         -- TODO(joel) - better description
         "introduce new module parameters or hypotheses"
         [ ("<labels>", "One or more names to introduce")
         , ("<type>", "(optional) their type")
         ]
     )


letTac = simpleCT
    "let"
    Historic
    "introduce new module parameters or hypotheses"
    (TfBlockSequence
        [ TfName "label" -- (Just "Name to introduce")
        , TfScheme "scheme" Nothing -- XXX
        ]
    )
    (\(TrSequence [ TrName name, TrScheme scheme ]) -> do
        let name' = T.unpack name
        elabLet (name' :<: scheme)
        optional problemSimplify
        optional seekGoal
        return (fromString $ "Let there be " <> name' <> "."))
    (TacticHelp
        "let <label> <scheme> : <type>"
        "let A (m : Nat) : Nat -> Nat"
        -- TODO(joel) - better description
        "introduce new module parameters or hypotheses"
        [ ("<labels>", "One or more names to introduce")
        , ("<type>", "(optional) their type")
        ]
    )


makeTac = simpleCT
    "make"
    Historic
    "the first form creates a new goal of the given type; the second adds a definition to the context"
    (TfInlineSequence
        [ TfName "x"
        , TfOption (TfInArg "term" Nothing)
        , TfInArg "type" Nothing
        ]
    )
    (\(TrSequence
        [ TrName name
        , TrOption maybeTerm
        , TrInArg ty
        ]
      ) -> let name' = T.unpack name in case maybeTerm of
          Just (TrInArg term) -> do
              elabMake (name' :<: ty)
              goIn
              elabGive term
              return "Made."
          Nothing -> do
              elabMake (name' :<: ty)
              goIn
              return "Appended goal!"
    )
    (TacticHelp
        "make <x> : <type> OR make <x> := <term> : <type>"
        "make A := ? : Set"
        -- TODO(joel) - better description
        "the first form creates a new goal of the given type; the second adds a definition to the context"
        [ ("<x>", "New name to introduce")
        , ("<term>", "its definition (this could be a hole (\"?\"))")
        , ("<type>", "its type (this could be a hole (\"?\"))")
        ]
    )


moduleTac = unaryStringCT "module"
    (\name -> do
        makeModule DevelopModule (T.unpack name)
        goIn
        return "Made module."
    )
    "creates a module with name <x>."


piTac = simpleCT
    "pi"
    Historic
    "introduce a pi"
    (TfInlineSequence
        [ TfName "x"
        , TfKeyword KwAsc
        , TfInArg "type" Nothing
        ]
    )
    (\(TrSequence [ TrName name, TrKeyword, TrInArg ty ]) -> do
        elabPiParam (T.unpack name :<: ty)
        return "Made pi!"
    )
    (TacticHelp
        "pi <x> : <type>"
        "pi A : Set"
        -- TODO(joel) - better description
        "introduce a pi (what's a pi?)"
        [ ("<x>", "Pi to introduce")
        , ("<type>", "its type")
        ]
    )


programTac = simpleCT
    "program"
    Historic
    "set up a programming problem"
    (TfSep (TfName "label") KwComma)
    (\(TrSep as) -> do
        elabProgram (map (T.unpack . argToStr) as)
        return "Programming."
    )
    (TacticHelp
        "program <labels>"
        "(make plus : Nat -> Nat -> Nat) ; program x, y ;"
        -- TODO(joel) - better description
        "set up a programming problem"
        [ ("<labels>", "One or more names to introduce")
        ]
    )


doitTac = simpleCT
    "demoMagic"
    Historic
    "pigment tries to implement it for you"
    (TfInlineSequence [])
    (\_ -> assumption >> return "Did it!")
    (TacticHelp
        "demoMagic"
        "demoMagic"
        "pigment tries to implement it for you"
        []
    )

autoTac = simpleCT
    "auto"
    Historic
    "coq's auto"
    (TfInlineSequence [])
    (\_ -> auto >> return "Auto... magic!")
    (TacticHelp
        "auto"
        "auto"
        "coq's auto"
        []
    )


-- ungawa: Word used by tarzan to communicate with animals? Also by chance
-- it's Swahili for "to unite" or "to join"
-- TODO(joel) - rename
ungawaTac = nullaryCT "ungawa" Historic (ungawa >> return "Ungawa!")
    "tries to solve the current goal in a stupid way."


-- Navigation Tactics
inTac = nullaryCT "in" Forgotten (goIn >> return "Going in...")
    "moves to the bottom-most development within the current one."


outTac = nullaryCT "out" Forgotten (goOutBelow >> return "Going out...")
    "moves to the development containing the current one."


upTac = nullaryCT "up" Forgotten (goUp >> return "Going up...")
    "moves to the development above the current one."


downTac = nullaryCT "down" Forgotten (goDown >> return "Going down...")
    "moves to the development below the current one."


topTac = nullaryCT "top" Forgotten (many goUp >> return "Going to top...")
    "moves to the top-most development at the current level."


bottomTac = nullaryCT
    "bottom"
    Forgotten
    (many goDown >> return "Going to bottom...")
    "moves to the bottom-most development at the current level."


previousTac = nullaryCT
    "previous"
    Forgotten
    (prevGoal >> return "Going to previous goal...")
    "searches for the previous goal in the proof state."


rootTac = nullaryCT
    "root"
    Forgotten
    (many goOut >> return "Going to root...")
    "moves to the root of the proof state."


nextTac = nullaryCT
    "next"
    Forgotten
    (nextGoal >> return "Going to next goal...")
    "searches for the next goal in the proof state."


firstTac = nullaryCT
    "first"
    Forgotten
    (some prevGoal >> return "Going to first goal...")
    "searches for the first goal in the proof state."


lastTac = nullaryCT
    "last"
    Forgotten
    (some nextGoal >> return "Going to last goal...")
    "searches for the last goal in the proof state."


jumpTac = unaryNameCT "jump" (\ x -> do
    (n := _) <- resolveDiscard x
    goTo n
    return $ fromString $ "Jumping to " ++ showName n ++ "..."
  )
    "moves to the definition of <name>."


-- Miscellaneous tactics
-- TODO(joel) visual display of previous states
undoTac = CochonTactic
    { ctName = "undo"
    , ctMessage = "undo"
    , ctDesc = TfInlineSequence []
    , ctxTrans = \_ -> do
          locs :< loc <- getCtx
          case locs of
              B0  -> tell "Cannot undo."  >> setCtx (locs :< loc)
              _   -> tell "Undone."       >> setCtx locs
    , ctHelp = TacticHelp
          "undo"
          "undo"
          "goes back to a previous state."
          []
    }


validateTac = nullaryCT "validate" Forgotten (validateHere >> return "Validated.")
    "re-checks the definition at the current location."


dataTac = CochonTactic
    {  ctName = "data"
    ,  ctMessage = "Create a new data type"
    ,  ctDesc = TfBlockSequence
           [ TfName "name"
           , TfRepeatZero (
                TfInlineSequence
                    [ TfName "parameter"
                    , TfKeyword KwAsc
                    , TfInArg "type" (Just "type of this parameter")
                    ]
                )
           , TfKeyword KwDefn
           , TfSep
                (TfInlineSequence
                    [ TfKeyword KwTag
                    , TfName "constructor"
                    , TfKeyword KwAsc
                    , TfInArg "type" (Just "type of this constructor")
                    ]
                )
                KwSemi
           ]
    , ctxTrans = \(TrSequence
        [ TrName name
        , TrRepeatZero pars
        , TrKeyword
        , TrSep cons
        ]) -> simpleOutput Historic $ do
            let pars' = undefined pars
                cons' = undefined cons
                name' = T.unpack name
                argToStr' = T.unpack . argToStr
            elabData name' (argList (argPair argToStr' argToIn) pars')
                           (argList (argPair argToStr' argToIn) cons')
            return "Data'd."
    ,  ctHelp = TacticHelp
           "data <name> [<para>]* := [(<con> : <ty>) ;]*"
           "data List (X : Set) := ('nil : List X) ; ('cons : X -> List X -> List X) ;"
           "Create a new data type"
           [ ("<name>", "Choose the name of your datatype carefully")
           , ("<para>", "Type parameters")
           , ("<con : ty>", "Give each constructor a unique name and a type")
           ]
    }


eliminateTac = simpleCT
    "eliminate"
    Historic
    "eliminate with a motive (same as <=)"
    (TfInlineSequence
        [ TfOption (TfName "comma")
        , TfAlternative (TfExArg "eliminator" Nothing, tfAscription)
        ]
    )
    (\(TrSequence [ TrOption maybeName, TrAlternative elim ]) ->
        undefined)
        -- elimCTactic (argOption (unDP . argToEx) n) (argToEx e))
    (TacticHelp
        "eliminate [<comma>] <eliminator>"
        "eliminate induction NatD m"
        -- TODO(joel) - better description
        "eliminate with a motive (same as <=)"
        [ ("<comma>", "TODO(joel)")
        , ("<eliminator>", "TODO(joel)")
        ]
    )


retTac = unaryInCT "=" (\tm -> elabGiveNext (DLRET tm) >> return "Solved.")
    "solves the programming problem by returning <term>."


defineTac = simpleCT
     "define"
    Historic
     "relabel and solve <prob> with <term>"
     (TfInlineSequence
        [ TfInArg "prob" Nothing
        , TfKeyword KwDefn
        , TfInArg "term" Nothing
        ]
    )
    (\(TrSequence [ TrExArg rl, TrInArg tm ]) -> defineCTactic rl tm)
    (TacticHelp
        "define <prob> := <term>"
        "define vappend 'zero 'nil k bs := bs"
        -- TODO(joel) - better description
        "relabel and solve <prob> with <term>"
        [ ("<prob>", "pattern to match and define")
        , ("<term>", "solution to the problem")
        ]
    )


-- The By gadget, written `<=`, invokes elimination with a motive, then
-- simplifies the methods and moves to the first subgoal remaining.
byTac = simpleCT
    "<="
    Historic
    "eliminate with a motive (same as eliminate)"
    (TfInlineSequence
        [ TfOption (TfName "comma")
        , TfAlternative (TfExArg "eliminator" Nothing, tfAscription)
        ]
    )
    -- XXX(joel)
    (\(TrSequence [ n, e ]) -> byCTactic (argOption (unDP . argToEx) n) (argToEx e))
    (TacticHelp
        "<= [<comma>] <eliminator>"
        "<= induction NatD m"
        -- TODO(joel) - better description
        "eliminate with a motive (same as eliminate)"
        [ ("<comma>", "TODO(joel)")
        , ("<eliminator>", "TODO(joel)")
        ]
    )


-- The Refine gadget relabels the programming problem, then either defines
-- it or eliminates with a motive.
refineTac = simpleCT
    "refine"
    Historic
    "relabel and solve or eliminate with a motive"
    (TfBlockSequence
        [ TfExArg "prob" Nothing
        , TfAlternative
            ((TfInlineSequence [ TfKeyword KwEq, TfInArg "term" Nothing ]),
            (TfInlineSequence
                [ TfKeyword KwBy
                , TfAlternative (TfExArg "prob" Nothing, tfAscription)
                ]
            ))
        ]
    )
    (\(TrSequence [ TrExArg rl, arg ]) -> case arg of
        TrInArg tm -> defineCTactic rl tm
        TrExArg tm -> relabel rl >> byCTactic Nothing tm)
    (TacticHelp
        "refine <prob> = <term> OR refine <prob> <= <eliminator>"
        "refine plus 'zero n = n"
        -- TODO(joel) - better description
        "relabel and solve or eliminate with a motive"
        [ ("<prob>", "TODO(joel)")
        , ("<term>", "TODO(joel)")
        , ("<prob>", "TODO(joel)")
        , ("<eliminator>", "TODO(joel)")
        ]
    )


solveTac = simpleCT
    "solve"
    Historic
    "solve a hole"
    (TfBlockSequence
        [ TfName "name"
        , TfInArg "term" Nothing
        ]
    )
    (\(TrSequence [ TrExArg (DP rn ::$ []), TrInArg tm ]) -> do
        (ref, spine, _) <- resolveHere rn
        _ :<: ty <- inferHere (P ref $:$ toSpine spine)
        _ :=>: tv <- elaborate' (ty :>: tm)
        tm' <- mQuote (SET :>: tv) -- force definitional expansion
        solveHole ref tm'
        return "Solved."
    )
    (TacticHelp
        "solve <name> <term>"
        "solve a hole"
        -- TODO(joel) - better description
        "make A := ? : Set; solve A Set"
        [ ("<name>", "The name of the hole to solve")
        , ("<term>", "Its solution")
        ]
    )


{-
idataTac = CochonTactic
    {  ctName = "idata"
    ,  ctDesc = (
        TfSequence
            [ "idata"
            , TfName "name"
            , TfRepeatZero (
                    -- TODO(joel) is this tfAscription? this is a thing.
                    -- what is this?
                    TfBracketed Round (TfSequence
                        [ TfName "para"
                        , TfKeyword KwAsc
                        , TfInArg "ty" Nothing
                        ])
                    )
            , TfKeyword KwAsc
            , TfInArg "inx" Nothing -- TODO(joel) - better name
            , TfKeyword KwArr
            , TfKeyword KwSet
            , TfKeyword KwDefn
            , TfRepeatZero (
                TfBracketed Round (TfRepeatZero
                    (TfSep
                        (TfSequence
                            [ TfKeyword KwTag
                            , TfName "con"
                            , TfKeyword KwAsc
                            , TfName "ty"
                            ]
                        )
                        KwSemi
                    )
                )
              )
            ]
        )
    , ctxTrans = \(TrSequence
        [ TrName nom
        , TrRepeatZero pars
        , TrKeyword
        , indty
        , TrKeyword
        , TrKeyword
        , TrKeyword
        , cons
        ]) -> simpleOutput Historic $ do
            ielabData
                nom
                (argList (argPair argToStr argToIn) pars)
                (argToIn indty)
                (argList (argPair argToStr argToIn) cons)
            return "Data'd."
    , ctHelp = TacticHelp
           "idata <name> [<para>]* : <inx> -> Set  := [(<con> : <ty>) ;]*"
           "idata Vec (A : Set) : Nat -> Set := ('cons : (n : Nat) -> (a : A) -> (as : Vec A n) -> Vec A ('suc n)) ;"
           "Create a new indexed data type"
           [ ("<name>", "Choose the name of your datatype carefully")
           , ("<para>", "Type parameters")
           , ("<inx>", "??")
           , ("<con : ty>", "Give each constructor a unique name and a type")
           ]
    }
-}


{-
The `elm` Cochon tactic elaborates a term, then starts the scheduler to
stabilise the proof state, and returns a pretty-printed representation
of the final type-term pair (using a quick hack).
-}
elmCT :: DExTmRN -> ProofState String
elmCT tm = do
    suspend ("elab" :<: sigSetTM :=>: sigSetVAL) (ElabInferProb tm)
    startScheduler
    infoElaborate (DP [("elab", Rel 0)] ::$ [])


elmTac = unaryExCT "elm" elmCT "elm <term> - elaborate <term>, stabilise and print type-term pair."


elaborateTac = unaryExCT "elaborate" infoElaborate
  "elaborate <term> - elaborates, evaluates, quotes, distills and pretty-prints <term>."


-- TEMP(joel)
elabTac = unaryExCT "elab" infoElaborate
  "elab <term> - elaborates, evaluates, quotes, distills and pretty-prints <term>."


inferTac = unaryExCT "infer" infoInfer
  "infer <term> - elaborates <term> and infers its type."


parseTac = unaryInCT "parse" (return . fromString . show)
  "parses <term> and displays the internal display-sytnax representation."


-- schemeTac = unaryNameCT "scheme" infoScheme
--   "looks up the scheme on the definition <name>."


dumpTac = nullaryCT "dump"
    Forgotten
    (fromString <$> prettyProofState)
    "displays useless information."


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
    Historic
    "match parameters in first term against second."
    (TfBlockSequence
        [ TfRepeatZero -- XXX(joel) - RepeatOne?
            (TfBracketed Round
                (TfInlineSequence
                    [ TfName "tm"
                    , TfKeyword KwAsc
                    , TfInArg "ty" Nothing
                    ]
                )
            )
        , TfKeyword KwSemi
        , TfExArg "term" Nothing
        , TfKeyword KwSemi
        , TfInArg "term" Nothing
        ]
    )
    (\(TrSequence [ TrRepeatZero pars, TrExArg a, TrInArg b ]) ->
        matchCTactic (map (argPair argToStr argToIn) pars) a b)
    (TacticHelp
        "match [<para>]* ; <term> ; <term>"
        "TODO(joel)"
        -- TODO(joel) - better description
        "match parameters in first term against second."
        [ ("<para>", "TODO(joel)")
        , ("<term>", "TODO(joel)")
        ]
    )


simplifyTac = nullaryCT
    "simplify"
    Historic
    (problemSimplify >> optional seekGoal >> return "Simplified.")
    "simplifies the current problem."

{-
TODO(joel) - how did this ever work? pars is not bound here either
https://github.com/joelburget/pigment/blob/bee79687c30933b8199bd9ae6aaaf8048a0c1cf9/src/Tactics/Record.lhs

recordTac = CochonTactic
    {  ctName = "record"
    , ctIO = (\ [StrArg nom, pars, cons] -> simpleOutput Historic $
                elabRecord nom (argList (argPair argToStr argToIn) pars)
                               (argList (argPair argToStr argToIn) cons)
                  >> return "Record'd.")
    ,  ctHelp = "record <name> [<para>]* := [(<label> : <ty>) ;]* - builds a record type."
    }
-}


relabelTac = unaryExCT "relabel" (\ ex -> relabel ex >> return "Relabelled.")
    "relabel <pattern> - changes names of arguments in label to pattern"


-- end tactics, begin a bunch of weird "info" stuff and other helpers
-- The `propSimplify` tactic attempts to simplify the type of the current
-- goal, which should be propositional. Usually one will want to use
-- `simplify` instead, or simplification will happen automatically (with
-- the `let` and `<=` tactics), but this is left for backwards
-- compatibility.
--
-- propsimplifyTac = nullaryCT "propsimplify" propSimplifyTactic
--     "applies propositional simplification to the current goal."
propSimplifyTactic :: ProofState String
propSimplifyTactic = do
    subs <- propSimplifyHere
    case subs of
        B0  -> return "Solved."
        _   -> do
            subStrs <- traverse prettyType subs
            nextGoal
            return $ fromString ("Simplified to:\n" ++
                Foldable.foldMap (++ "\n") subStrs)
  where
    prettyType :: INTM -> ProofState String
    prettyType ty = liftM renderHouseStyle (prettyHere (SET :>: ty))


-- The `infoElaborate` command calls `elabInfer` on the given neutral
-- display term, evaluates the resulting term, bquotes it and returns a
-- pretty-printed string representation. Note that it works in its own
-- module which it discards at the end, so it will not leave any subgoals
-- lying around in the proof state.
infoElaborate :: DExTmRN -> ProofState String
infoElaborate tm = draftModule "__infoElaborate" $ do
    (tm' :=>: tmv :<: ty) <- elabInfer' tm
    tm'' <- mQuote (ty :>: tmv)
    tellTermHere (ty :>: tm'')


-- The `infoInfer` command is similar to `infoElaborate`, but it returns a
-- string representation of the resulting type.
infoInfer :: DExTmRN -> ProofState String
infoInfer tm = draftModule "__infoInfer" $ do
    (_ :<: ty) <- elabInfer' tm
    ty' <- mQuote (SET :>: ty)
    tellTermHere (SET :>: ty')


-- infoScheme :: RelName -> ProofState String
-- infoScheme x = do
--     (_, as, ms) <- resolveHere x
--     case ms of
--         Just sch -> do
--             sch' <- distillSchemeHere (applyScheme sch as)
--             return $ reactify sch'
--         Nothing -> return $
--             fromString (showRelName x ++ " does not have a scheme.")


-- The `infoWhatIs` command displays a term in various representations.
infoWhatIs :: DExTmRN -> ProofState String
infoWhatIs tmd = draftModule "__infoWhatIs" $ do
    tm :=>: tmv :<: tyv <- elabInfer' tmd
    tmq <- mQuote (tyv :>: tmv)
    tms :=>: _ <- distillHere (tyv :>: tmq)
    ty <- mQuote (SET :>: tyv)
    tys :=>: _ <- distillHere (SET :>: ty)
    return $ mconcat
        [  "Parsed term:", fromString (show tmd)
        ,  "Elaborated term:", fromString (show tm)
        ,  "Quoted term:", fromString (show tmq)
        ,  "Distilled term:", fromString (show tms)
        ,  "Pretty-printed term:", fromString (renderHouseStyle (pretty tms maxBound))
        ,  "Inferred type:", fromString (show tyv)
        ,  "Quoted type:", fromString (show ty)
        ,  "Distilled type:", fromString (show tys)
        ,  "Pretty-printed type:", fromString (renderHouseStyle (pretty tys maxBound))
        ]

byCTactic :: Maybe RelName -> DExTmRN -> ProofState String
byCTactic n e = do
    elimCTactic n e
    optional problemSimplify           -- simplify first method
    many (goDown >> problemSimplify)   -- simplify other methods
    many goUp                          -- go back up to motive
    optional seekGoal                  -- jump to goal
    return "Eliminated and simplified."

defineCTactic :: DExTmRN -> DInTmRN -> ProofState String
defineCTactic rl tm = do
    relabel rl
    elabGiveNext (DLRET tm)
    return "Hurrah!"

matchCTactic :: [(Text, DInTmRN)]
             -> DExTmRN
             -> DInTmRN
             -> ProofState String
matchCTactic xs a b = draftModule "__match" $ do
    rs <- traverse matchHyp xs
    (_ :=>: av :<: ty) <- elabInfer' a
    cursorTop
    (_ :=>: bv) <- elaborate' (ty :>: b)
    rs' <- runStateT (matchValue B0 (ty :>: (av, bv))) (bwdList rs)
    return (fromString (show rs'))
  where
    matchHyp :: (Text, DInTmRN) -> ProofState (REF, Maybe VAL)
    matchHyp (s, t) = do
        tt  <- elaborate' (SET :>: t)
        r   <- assumeParam (T.unpack s :<: tt)
        return (r, Nothing)

elimCTactic :: Maybe RelName -> DExTmRN -> ProofState String
elimCTactic c r = do
    c' <- traverse resolveDiscard c
    (e :=>: _ :<: elimTy) <- elabInferFully r
    elim c' (elimTy :>: e)
    toFirstMethod
    return "Eliminated. Subgoals awaiting work..."


simpleOutput :: Historic -> ProofState String -> Cmd ()
simpleOutput hist eval = do
    locs :< loc <- getCtx
    case runProofState (eval <* startScheduler) loc of
        Left err -> do
            setCtx (locs :< loc)
            tell "I'm sorry, Dave. I'm afraid I can't do that."
        Right (msg, loc') -> do
            setCtx $ case hist of
                Historic -> locs :< loc :< loc'
                Forgotten -> locs :< loc'
            tell msg
