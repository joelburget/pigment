{-# LANGUAGE GADTs, TypeOperators, PatternSynonyms, FlexibleInstances, MultiParamTypeClasses #-}

module Tactics.Matching (
    -- * Matching substitutions
      MatchSubst
    , elemSubst
    , insertSubst
    -- $commands
    , matchValue
    , chevMatchValue
    , matchNeutral
    , checkSafe
    ) where

import Prelude hiding (any, elem)
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Class
import Data.Foldable
import Data.String (fromString)

import Control.Error

import DisplayLang.Name
import NameSupply.NameSupplier
import Evidences.Tm
import Evidences.Eval
import Evidences.Operators
import Evidences.DefinitionalEquality
import Evidences.PropositionalEquality
import Evidences.TypeChecker
import ProofState.Edition.ProofState
import ProofState.Interface.ProofKit
import Kit.BwdFwd
import Kit.MissingLibrary

-- | A *matching substitution* is a list of references with their values, if
-- any.
type MatchSubst = Bwd (REF, Maybe VAL)

-- | It is easy to decide if a reference is an element of such a
-- substitution:
elemSubst :: REF -> MatchSubst -> Bool
elemSubst r = any ((r ==) . fst)

-- | When inserting a new reference-value pair into the substitution, we
-- ensure that it is consistent with any value already given to the
-- reference.
insertSubst :: REF
            -> VAL
            -> StateT MatchSubst ProofState ()
insertSubst x t = get >>= (`help` F0)
  where
    help :: MatchSubst
         -> Fwd (REF, Maybe VAL)
         -> StateT MatchSubst ProofState ()
    help B0 fs = lift $ throwDTmStr "insertSubst: reference not found!"
    help (rs :< (y, m)) fs | x == y = case m of
        Nothing  -> put (rs :< (x, Just t) <>< fs)
        Just u   -> do
            eq <- lift $ withNSupply (equal (pty x :>: (t, u)))
            if eq
                then put (rs :< (y, m) <>< fs)
                else lift $ throwDTmStr "insertSubst: match failed"
    help (rs :< (y, m)) fs = help rs ((y, m) :> fs)

-- $commands
-- The matching commands, defined below, take a matching substitution
-- (initially with no values for the references) and a pair of objects. The
-- references must only exist in the first object, and each reference may
-- only depend on those before it (in the usual telescopic style). Each
-- command will produce an updated substitution, potentially with more
-- references defined.
--
-- Note that the resulting values may contain earlier references that need
-- to be substituted out. Any references left with no value at the end are
-- unconstrained by the matching problem.

-- | The `matchValue` command requires the type of the values to be pushed
-- in. It expands elements of $\Pi$-types by applying them to fresh
-- references, which must not occur in solution values (this might
-- otherwise happen when given a higher-order matching problem with no
-- solutions). The fresh references are therefore collected in a list and
-- `checkSafe` (defined below) is called to ensure none of the unsafe
-- references occur.
matchValue :: Bwd REF
           -> TY :>: (VAL, VAL)
           -> StateT MatchSubst ProofState ()
matchValue zs (ty :>: (NP x, t)) = do
    rs <- get
    if x `elemSubst` rs
        then  lift (checkSafe zs t) >> insertSubst x t
        else  matchValue' zs (ty :>: (NP x, t))
matchValue zs tvv = matchValue' zs tvv

matchValue' :: Bwd REF
            -> TY :>: (VAL, VAL)
            -> StateT MatchSubst ProofState ()
matchValue' zs (PI s t :>: (v, w)) = do
    rs <- get
    rs' <- lift $ freshRef ("expand" :<: s) $ \ sRef -> do
        let sv = pval sRef
        execStateT (matchValue (zs :< sRef) (t $$ A sv :>: (v $$ A sv, w $$ A sv))) rs
    put rs'
matchValue' zs (C cty :>: (C cs, C ct)) = case halfZip cs ct of
    Nothing   -> lift $ throwDTmStr "matchValue: unmatched constructors!"
    Just cst  -> do
        (mapStateT $ mapStateT $ liftError'
            (\ v -> convertErrorVALs (fmap fst v)))
            (canTy (chevMatchValue zs) (cty :>: cst))
        return ()

matchValue' zs (_ :>: (N s, N t)) = matchNeutral zs s t >> return ()
matchValue' zs tvv = lift $ do
    matches <- withNSupply $ equal tvv
    unless matches $ throwDTmStr "matchValue' failed"

chevMatchValue :: Bwd REF
               -> TY :>: (VAL, VAL)
               -> StateT MatchSubst (ProofStateT (VAL, VAL)) (() :=>: VAL)
chevMatchValue zs tvv@(_ :>: (v, _)) = do
    (mapStateT $ liftErrorState (error "matchValue: unconvertable error!"))
        $ matchValue zs tvv
    return (() :=>: v)

-- | The `matchNeutral` command matches two neutrals, and returns their type
-- along with the matching substitution.

matchNeutral :: Bwd REF
             -> NEU
             -> NEU
             -> StateT MatchSubst ProofState TY
matchNeutral zs (P x) t = do
    rs <- get
    if x `elemSubst` rs
        then do
            lift $ checkSafe zs (N t)
            insertSubst x (N t)
            return (pty x)
        else matchNeutral' zs (P x) t
matchNeutral zs a b = matchNeutral' zs a b

matchNeutral' :: Bwd REF
              -> NEU
              -> NEU
              -> StateT MatchSubst ProofState TY
matchNeutral' zs (P x)  (P y)
    | x == y
    = return (pty x)
matchNeutral' zs (f :$ e) (g :$ d)
    = do
        C ty <- matchNeutral zs f g
        case halfZip e d of
            Nothing -> lift $
                throwDTmStr "matchNeutral: unmatched eliminators!"
            Just ed -> do
                (_, ty') <- unconvertable' $
                    elimTy (chevMatchValue zs) (N f :<: ty) ed
                return ty'
matchNeutral' zs (fOp :@ as) (gOp :@ bs)
    | fOp == gOp
    = do
        (_, ty) <- unconvertable' $ opTy fOp (chevMatchValue zs) (zip as bs)
        return ty
matchNeutral' zs a b = lift $ throwDInTmRN $ stackItem
    [ errMsg "matchNeutral: unmatched "
    , errVal (N a)
    , errMsg "and"
    , errVal (N b)
    ]

unconvertable' :: StateT MatchSubst (ProofStateT (VAL, VAL)) a
               -> StateT MatchSubst (ProofStateT DInTmRN) a
-- XXX(joel)
unconvertable' st = StateT $ \s ->
    let pfSt = runStateT st s
    in liftErrorState unconvertable pfSt

unconvertable = error "matchNeutral: unconvertable error!"

-- | As noted above, fresh references generated when expanding Pi-types
-- must not occur as solutions to matching problems. The `checkSafe`
-- function throws an error if any of the references occur in the value.
checkSafe :: Bwd REF -> VAL -> ProofState ()
checkSafe zs t  | any (`elem` t) zs  = throwDTmStr "checkSafe: unsafe!"
                | otherwise          = return ()
