<a name="ProofState.Structure.Entries">Managing Entries in a Development</a>
=================================

> {-# LANGUAGE FlexibleInstances, TypeOperators, GADTs, PatternSynonyms #-}

> module ProofState.Structure.Entries where

> import Data.Traversable
> import NameSupply.NameSupply
> import Evidences.Tm
> import DisplayLang.Scheme
> import ProofState.Structure.Developments

Looking into an `Entry`
-----------------------

In the following, we define a bunch of helper functions to access
specific fields of an `Entry`. The field we look for might not exist for
all possible `Entry`, therefore we work in a `Maybe` world. The naming
rule of thumb of these function is: prefix `entry` followed by the name
of one field of the `E` or `M` cases, starting with a capital letter.

Hence, we have:

> entryRef :: Traversable f => Entry f -> Maybe REF
> entryRef (EEntity r _ _ _ _ _) = Just r
> entryRef EModule{}             = Nothing

> entryName :: Traversable f => Entry f -> Name
> entryName (EEntity (n := _) _ _ _ _ _) = n
> entryName (EModule n _ _ _)            = n

> entryLastName :: Traversable f => Entry f -> (String, Int)
> entryLastName (EEntity _ xn _ _ _ _) = xn
> entryLastName (EModule n _ _ _)      = last n

> entryScheme :: Traversable f => Entry f -> Maybe (Scheme INTM)
> entryScheme (EDEF _ _ (PROG sch) _ _ _ _) = Just sch
> entryScheme _                             = Nothing

> entryDev :: Traversable f => Entry f -> Maybe (Dev f)
> entryDev (EDEF _ _ _ d _ _ _) = Just d
> entryDev (EModule _ d _ _)    = Just d
> entryDev EPARAM{}             = Nothing

> entrySuspendState :: Traversable f => Entry f -> SuspendState
> entrySuspendState e = case entryDev e of
>     Just dev  -> devSuspendState dev
>     Nothing   -> SuspendNone

> entryAnchor :: Traversable f => Entry f -> EntityAnchor
> entryAnchor (EEntity _ _ _ _ anchor _)  = anchor
> entryAnchor EModule{}                   = AnchNo

> entryExpanded :: Traversable f => Entry f -> Bool
> entryExpanded (EEntity _ _ _ _ _ e) = e
> entryExpanded (EModule _ _ e _    ) = e

Entry equality
--------------

Two entries are equal if and only if they have the same name:

> instance Traversable f => Eq (Entry f) where
>     e1 == e2 = entryName e1 == entryName e2

Changing the carrier of an `Entry`
----------------------------------

The `entryCoerce` function is quite a thing. When defining `Dev`, we
have been picky in letting any Traversable `f` be the carrier of the `f
(Entry f)`. As shown in Section [ProofState.Edition.ProofContext](#ProofState.Edition.ProofContext),
we sometimes need to jump from one Traversable `f` to another
Traversable `g`. In this example, we jump from a `NewsyFwd` – a `Fwd`
list – to some `Entries` – a `Bwd` list.

Changing the type of the carrier is possible for parameters, in which
case we return a `Right entry`. It is not possible for definitions and
modules, in which case we return an unchanged `Left dev`.

> entryCoerce ::  (Traversable f, Traversable g) =>
>                 Entry f -> Either (Dev f) (Entry g)
> entryCoerce param@(EPARAM ref xn k ty anchor expanded) =
>     Right $ EPARAM ref xn k ty anchor expanded
> entryCoerce (EDEF _ _ _ dev _ _ _)     =  Left dev
> entryCoerce (EModule _ dev _ _)        =  Left dev
