Name management
===============

> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Interface.Name where

> import Data.Foldable
> import Data.Monoid

> import NameSupply.NameSupply
> import ProofState.Structure.Developments
> import ProofState.Structure.Entries
> import ProofState.Edition.Scope
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import Evidences.Tm
> import Evidences.Operators

The `lookupName` function looks up a name in the context (including
axioms and primitives); if found, it returns the reference applied to
the spine of shared parameters.

> lookupName :: Name -> ProofStateT e (Maybe (EXTM :=>: VAL))
> lookupName name = do
>     inScope <- getInScope
>     case find ((name ==) . entryName) inScope of
>       Just (EEntity ref _ _ _ _ _) -> return $ Just $ applySpine ref inScope
>       Nothing ->
>         case find ((name ==) . refName . snd) primitives of
>           Just (_, ref)  -> return $ Just $ applySpine ref inScope
>           Nothing        -> return Nothing

The `pickName` command takes a prefix suggestion and a name suggestion
(either of which may be empty), and returns a more-likely-to-be-unique
name if the name suggestion is empty.

XXX(joel) - this picks poor names

> pickName :: String -> EntityAnchor -> ProofState String
> pickName prefix AnchNo = pickName' prefix
> pickName prefix (AnchStr "") = pickName' prefix
> pickName prefix s   = return $ prefix ++ show s

> pickName' :: String -> ProofState String
> pickName' prefix = do
>     m <- getCurrentName
>     r <- getDevNSupply
>     let suffix = getSum (foldMap (Sum . snd) m) + snd r
>         prefix' = if prefix == "" then "x" else prefix
>     return $ prefix' ++ show suffix
