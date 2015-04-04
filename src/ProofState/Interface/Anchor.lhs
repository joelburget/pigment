Anchor resolution
=================

> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes, PatternSynonyms #-}

> module ProofState.Interface.Anchor where

> import Control.Applicative
> import Data.Foldable
> import Data.Traversable
> import Data.Monoid

> import Kit.MissingLibrary
> import Kit.BwdFwd
> import ProofState.Structure.Developments
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import Evidences.Tm

> isAnchor :: Traversable f => Entry f -> Bool
> isAnchor (EEntity _ _ _ _ AnchNo _)  = False
> isAnchor _                           = True

> anchorsInScope :: ProofState Entries
> anchorsInScope = do
>   scope <- getInScope
>   return $ foldMap anchors scope
>       where anchors t | isAnchor t = B0 :< t
>                       | otherwise  = B0

To cope with shadowing, we will need some form of `RelativeAnchor`:

< type RelativeAnchor = (Anchor, Int)

With shadowing punished by De Bruijn. Meanwhile, let's keep it simple.

> resolveAnchor :: EntityAnchor -> ProofStateT e (Maybe REF)
> resolveAnchor anchor = do
>   scope <- getInScope
>   case seekAnchor scope of
>     B0 -> return Nothing
>     _ :< ref -> return $ Just ref
>     where seekAnchor :: Entries -> Bwd REF
>           seekAnchor B0 = empty
>           seekAnchor (scope :< EPARAM ref _ _ _ anchor' _)
>                            | anchor' == anchor = B0 :< ref
>           seekAnchor (scope :< EPARAM ref _ _ _ AnchNo _) = seekAnchor scope
>           seekAnchor (scope :< EDEF ref _ _ dev _ AnchNo _) =
>                         seekAnchor (devEntries dev)
>                         <> seekAnchor scope
>           seekAnchor (scope :< EDEF ref _ _ dev _ anchor' _)
>                            | anchor' == anchor = B0 :< ref
>           seekAnchor (scope :< EModule _ dev _ _) =
>                         seekAnchor (devEntries dev)
>                         <> seekAnchor scope

Find the entry corresponding to the given anchor:

> findAnchor :: String -> ProofState ()
> findAnchor = undefined

Redefine the entry corresponding from the given anchor, so that's name
is the second anchor:

> renameAnchor :: String -> String -> ProofState ()
> renameAnchor = undefined
