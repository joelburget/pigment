<a name="ProofState.Interface.ProofKit">The `ProofState` Kit</a>
====================

> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes, DataKinds #-}

> module ProofState.Interface.ProofKit where

> import Control.Error
> import Control.Monad
> import Control.Monad.Trans.Class

> import Kit.BwdFwd
> import Kit.MissingLibrary
> import NameSupply.NameSupply
> import NameSupply.NameSupplier
> import ProofState.Edition.ProofContext
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import Evidences.Tm
> import Evidences.TypeChecker

The proof state lives on a rich substrate of operations, inherited from
the `ProofContext` as well as the `ProofState` monad. In this module, we
export these operations as part of the Interface.

Accessing the `NameSupply`
--------------------------

By definition of the `Development` in
Section [ProofState.Structure.Developments](#ProofState.Structure.Developments),
we have that every entry is associated a namespace by the mean of a local name
supply. As a result, the `ProofState` can almost be made a `NameSupplier`. The
exception being that it cannot fork the name supply, because it cannot
generates new namespaces.

> instance NameSupplier (ProofStateT e) where
>     freshRef (s :<: ty) f = do
>         nsupply <- getDevNSupply
>         freshRef (s :<: ty) ( \ref nsupply' -> do
>             putDevNSupply nsupply'
>             f ref
>           ) nsupply
>     forkNSupply _ _ _ =
>         lift (Left (errMsgStack "ProofState does not provide forkNSupply"))
>     askNSupply = getDevNSupply

We also provide an operator to lift functions from a name supply to
proof state commands.

> withNSupply :: (NameSupply -> x) -> ProofStateT e x
> withNSupply f = getDevNSupply >>= return . f

[Read-only name supply]

Note that this function has no way to return an updated name supply to
the proof context, so it must not leave any references around when it
has finished.

Accessing the type-checker
--------------------------

Secondly, any type-checking problem (defined in the `Check` monad) can
be executed in the `ProofState`.

> runCheckHere :: (ErrorTok e -> ErrorTok DInTmRN)
>              -> Check e a
>              -> ProofState a
> runCheckHere f c =
>     join $ withNSupply $ lift . liftError' f . typeCheck c

As a consequence, we have `checkHere` to `check` terms against types:

> checkHere :: (TY :>: INTM) -> ProofState (INTM :=>: VAL)
> checkHere tt = runCheckHere (fmap DTIN) $ check tt

and `inferHere` to `infer` types from terms:

> inferHere :: EXTM -> ProofState (VAL :<: TY)
> inferHere tm = runCheckHere (fmap DTIN) $ infer tm

Being paranoiac
---------------

The `validateHere` command performs some sanity checks on the current
location, which may be useful for paranoia purposes.

> validateHere :: ProofState ()
> validateHere = do
>     m <- getCurrentEntry
>     case m of
>         CDefinition _ (_ := DEFN tm :<: ty) _ _ _ _ -> do
>             checkHere (SET :>: ty)
>                 `pushError` (stackItem
>                     [ errMsg "validateHere: definition type failed to type-check: SET does not admit"
>                     , errTyVal (ty :<: SET)
>                     ] :: StackError DInTmRN)
>             checkHere (ty :>: tm)
>                 `pushError` (stackItem
>                     [ errMsg "validateHere: definition failed to type-check:"
>                     , errTyVal (ty :<: SET)
>                     , errMsg "does not admit"
>                     , errTyVal (tm :<: ty)
>                     ] :: StackError DInTmRN)
>             return ()
>         CDefinition _ (_ := HOLE _ :<: ty) _ _ _ _ -> do
>             checkHere (SET :>: ty)
>                 `pushError` (stackItem
>                     [ errMsg "validateHere: hole type failed to type-check: SET does not admit"
>                     , errTyVal (ty :<: SET)
>                     ] :: StackError DInTmRN)
>             return ()
>         _ -> return ()
