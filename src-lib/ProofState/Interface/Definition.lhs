Making Definitions
==================

> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}
> module ProofState.Interface.Definition where
> import Kit.BwdFwd
> import Kit.MissingLibrary
> import NameSupply.NameSupply
> import ProofState.Structure.Developments
> import ProofState.Edition.Scope
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Interface.Lifting
> import ProofState.Interface.Name
> import ProofState.Interface.ProofKit
> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import Evidences.Tm
> import Evidences.Eval

The `make` command adds a named goal of the given type above the cursor.
The meat is actually in `makeKinded`, below.

> make :: String :<: INTM -> ProofState (EXTM :=>: VAL)
> make = makeKinded Waiting

When making a new definition, the reference to this definition bears a *hole
kind* (Section [Evidences.Tm.references](#Evidences.Tm.references)).
User-generated goals are of kind `Waiting`: waiting for the user to solve it
(or, if lucky, an automation tool could nail it down). For making these kind of
definition, we will use the `make` command above. However, during Elaboration
for instance (Section [Elaborator.Elaborator](#Elaborator.Elaborator)), the
proof system will insert goals itself, with a somewhat changing mood such as
`Hoping` or `Crying`.

> makeKinded :: HKind -> (String :<: INTM) -> ProofState (EXTM :=>: VAL)
> makeKinded holeKind (name :<: ty) = do
>     -- Check that the type is indeed a type
>     _ :=>: tyv <- checkHere (SET :>: ty)
>                     `pushError`
>                     (stackItem
>                         [ errMsg "make: "
>                         , errTm (DTIN ty)
>                         , errMsg " is not a set."
>                         ] :: StackError DInTmRN)

>     -- Make a name for the goal, from `name`
>     nsupply <- getDevNSupply
>     -- TODO(joel) this is so weird. How should making a name work here?
>     n <- pickName "" (mkName nsupply name)
>     let goalName = mkName nsupply n

>     -- Make a reference for the goal, with a lambda-lifted type
>     inScope <- getInScope
>     let  liftedTy  =  liftType inScope ty
>          ref       =  goalName := HOLE holeKind :<: evTm liftedTy

>     -- Make an entry for the goal, with an empty development
>     let dev = Dev { devEntries       =  B0
>                   , devTip           =  Unknown (ty :=>: tyv)
>                   , devNSupply       =  freshNSpace nsupply n
>                   , devSuspendState  =  SuspendNone }

>     -- Which kinds of things start out expanded? This is a very preliminary
>     -- list!
>     let expanded = True

>     -- Put the entry in the proof context
>     putDevNSupply $ freshName nsupply
>     putEntryAbove $ EDEF ref (last goalName) LETG dev liftedTy emptyMetadata

>     -- Return a reference to the goal
>     return $ applySpine ref inScope
