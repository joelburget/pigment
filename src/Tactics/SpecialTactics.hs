{-# LANGUAGE OverloadedStrings, GADTs, PatternSynonyms, DataKinds,
  LambdaCase, LiberalTypeSynonyms, MultiParamTypeClasses, TypeOperators #-}

module Tactics.SpecialTactics where

import Control.Applicative hiding (empty)
import qualified Data.Foldable as Foldable
import Data.Traversable
-- import Data.Text as T

import DisplayLang.DisplayTm
import DisplayLang.Name
import Kit.BwdFwd
import Kit.Trace
import Evidences.Tm
import ProofState.Edition.GetSet
import ProofState.Edition.ProofState
import qualified ProofState.Interface.Solving as Solving
import ProofState.Structure.Developments
import ProofState.Structure.Entries

import Tactics.ProblemSimplify

-- we need to know:
-- * how big the proof search space is!
-- * where we are in it!
-- * how many solutions there are
--
-- Sounds like a Foldable to me... Possibly a Traversable.

data SpecialTactic = SpecialTactic
    { action :: ProofState (EXTM :=>: VAL)
    , name :: String
    , description :: String -- T.Text
    }


-- giveTac :: SpecialTactic
-- giveTac = SpecialTactic
--     give
--     "give some term as the solution"

-- applyTac :: SpecialTactic
-- applyTac = SpecialTactic
--     apply
--     "apply a function (using its result)"

assumptionTac :: SpecialTactic
assumptionTac = SpecialTactic
    assumption
    "return"
    "return some applicable value in scope"

give :: INTM -> ProofState (EXTM :=>: VAL)
give = Solving.give

apply :: REF -> ProofState (EXTM :=>: VAL)
apply ref@(_ := _ :<: pi@(PI _ _)) = Solving.apply'' ref pi
apply _ = notFound

-- matchCTactic :: [(String, DInTmRN)]
--              -> DExTmRN
--              -> DInTmRN
--              -> ProofState (Bwd REF)


-- XXX(joel) - why EXTM?
-- Example:
--
--     matchGoal "f x" (\tm
matchGoal :: String -> EXTM -> ProofState ()
matchGoal tmPattern tm =
    case parse tokenize tmPattern of
        Left _ -> throwErrMsg "matchgoal: failed tokenize"
        Right tokens -> case parse pDInTm tokens of
            Left _ -> throwErrMsg "matchgoal: failed parse"
            Right intm -> matchCTactic

-- DEFN L ("A" :. L ("B" :. L ("a" :. L ("b" :. C (LRet N ((V 0 :$ A N (V 1))))))))

assumption :: ProofState (EXTM :=>: VAL)
assumption = do
    entries <- getInScope
    -- Try just returning the entry
    let f (EPARAM ref _ _ term _ _) =
            let justTm :: INTM
                justTm = NP ref
            in do elabTrace ("giving " ++ show justTm)
                  Solving.give (LRET justTm) -- <|> Solving.give (
        f _ = notFound
    -- ... for each entry
    foldl (<|>) notFound (map f (Foldable.toList entries))

-- The tactic auto works as follows. It first tries to call reflexivity and
-- assumption. If one of these calls solves the goal, the job is done.
-- Otherwise auto tries to apply the most recently introduced assumption that
-- can be applied to the goal without producing and error. This application
-- produces subgoals.  There are two possible cases. If the sugboals produced
-- can be solved by a recursive call to auto, then the job is done. Otherwise,
-- if this application produces at least one subgoal that auto cannot solve,
-- then auto starts over by trying to apply the second most recently introduced
-- assumption. It continues in a similar fashion until it finds a proof or
-- until no assumption remains to be tried.


auto :: ProofState (EXTM :=>: VAL)
auto = do
    entries <- getInScope
    let entryList = filter Solving.isParam $ Foldable.toList entries
    autoSpreader 5 entryList


autoSpreader :: Int
             -> [Entry Bwd]
             -> ProofState (EXTM :=>: VAL)
autoSpreader n entries = do
    let autoWith (x, xs) = auto' n (x:xs)
        subattempts = map autoWith (focuses' entries)
    elabTrace $ show (length entries) ++ " entries in scope"
    elabTrace $ show (length subattempts) ++ " subattempts"
    -- optional problemSimplify
    str <- Solving.prettyProofState
    elabTrace $ "autospreader proof state:"
    elabTrace $ str
    assumption <|> foldl (<|>) notFound subattempts

auto' :: Int -> [Entry Bwd] -> ProofState (EXTM :=>: VAL)
-- TODO(joel) figure out how to ensure this is shown if it happens! Don't
-- want it to be overwritten by an uninteresting shallower error.
auto' 0 _ = throwDTmStr "auto bottomed out!"
auto' _ [] = throwDTmStr "no valid parameter found"
auto' n (entry:entries) = do
    elabTrace $ "auto' " ++ (fst (last (entryName entry)))
    elabTrace $ "type: " ++ show (typeof entry)
    Solving.apply' entry
    autoSpreader (n-1) entries



-- utility

getParam :: Entry Bwd -> Maybe (Entry Bwd)
getParam e@(EPARAM _ _ _ _ _ _) = Just e
getParam _ = Nothing

focuses :: [a] -> [([a], a, [a])]
focuses []     = []
focuses (a:as) = ([], a, as):(map helper (focuses as))
    where helper (pres, focus, post) = ((a:pres), focus, post)


focuses' :: [a] -> [(a, [a])]
focuses' = map helper . focuses
    where helper (pres, focus, post) = (focus, pres ++ post)


notFound = throwDTmStr "no valid parameter found"


typeof :: Entry Bwd -> Maybe TY
typeof (EDEF (_ := _ :<: ty) _ _ _ _ _ _) = Just ty
typeof (EPARAM (_ := _ :<: ty) _ _ _ _ _) = Just ty
typeof _ = Nothing
