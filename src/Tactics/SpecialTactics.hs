{-# LANGUAGE OverloadedStrings, GADTs, PatternSynonyms, DataKinds,
  LambdaCase, LiberalTypeSynonyms, MultiParamTypeClasses, TypeOperators #-}

module Tactics.SpecialTactics where

import Control.Applicative hiding (empty)
import Data.Foldable
import Data.Traversable

import Evidences.Tm
import ProofState.Edition.ProofState
import qualified ProofState.Interface.Solving as Solving


-- we need to know:
-- * how big the proof search space is!
-- * where we are in it!
-- * how many solutions there are
--
-- Sounds like a Foldable to me... Possibly a Traversable.

type SpecialTactic = ProofState [EXTM :=>: VAL]

oneTargetTac :: ProofState (EXTM :=>: VAL) -> SpecialTactic
oneTargetTac = (pure <$>)

done :: SpecialTactic
done = oneTargetTac Solving.done

give :: INTM -> SpecialTactic
give tm = oneTargetTac Solving.give

apply :: REF -> SpecialTactic
apply (_ := _ :<: pi@(PI _ _)) =
    (pure <$> Solving.apply'' ref pi) <|> return []
apply _ = return []

assumption :: SpecialTactic
assumption = oneTargetTac $ do
    entries <- getInScope
    -- Try just returning the entry
    let f (EPARAM ref _ _ term _ _) =
            let justTm :: INTM
                justTm = NP ref
            in do elabTrace ("giving " ++ show justTm)
                  Solving.give (LRET justTm)
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


auto :: SpecialTactic
auto = do
    entries <- getInScope
    let entryList = filter isParam $ Foldable.toList entries
    autoSpreader 5 entryList
    -- let traversal :: Bwd (Maybe (Entry Bwd))
    --     traversal = do
    --         entries <- getInScope
    --         return $ traverse getParam entries

        -- estSize' :: Maybe (Entry Bwd) -> ProofState (

autoSpreader :: Int
             -> [Entry Bwd]
             -> SpecialTactic
autoSpreader n entries = do
    let autoWith (x, xs) = auto' n (x:xs)
        subattempts = map autoWith (focuses' entries)
    elabTrace $ show (length entries) ++ " entries in scope"
    elabTrace $ show (length subattempts) ++ " subattempts"
    (pure <$> done) <|>
        (do str <- prettyProofState
            elabTrace $ "autospreader proof state:"
            elabTrace $ str
            assumption <|> foldlM (<|>) notFound subattempts
        )

auto' :: Int -> [Entry Bwd] -> SpecialTactic
-- TODO(joel) figure out how to ensure this is shown if it happens! Don't
-- want it to be overwritten by an uninteresting shallower error.
auto' 0 _ = throwDTmStr "auto bottomed out!"
auto' _ [] = throwDTmStr "no valid parameter found"
auto' n (entry:entries) = do
    elabTrace $ "auto' " ++ (fst (last (entryName entry)))
    elabTrace $ "type: " ++ show (typeof entry)
    apply' entry
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
