Searching in the Proof Context
==============================

> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes, LambdaCase #-}

> module ProofState.Interface.Search where

> import Control.Applicative
> import Control.Monad

> import Lens.Family2

> import Kit.MissingLibrary
> import NameSupply.NameSupply
> import ProofState.Structure.Developments
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation
> import ProofState.Edition.ProofContext
> import Evidences.Tm
> import DisplayLang.Name


In Section [Proofstate.Edition.Navigation](#Proofstate.Edition.Navigation), we have developed
several commands to navigate in the proof context. Here, we extend these
to be able *search* in the proof context.

Searching by name
-----------------

The `goTo` command moves the focus to the entry with the given name.
Recall that a long name is an itinerary in the proof context, listing
short names from the root down to the entry. Hence, we simply have to
follow this itinerary to reach our destination.

> goTo :: Name -> ProofState ()
> goTo name = do
>   -- Start from the root
>   goRoot
>   -- Eat the name as you move in the context
>   goTo' name
>   where
>     couldNotFind x = stackItem
>         [ errMsg "goTo: could not find "
>         , errMsg x
>         ] :: StackError DInTmRN
>     goTo' :: Name -> ProofState ()
>     goTo'  []          =  return () -- Reached the end of the journey
>     goTo'  x@(xn:xns)  =  goIn >> seek xn >> goTo' xns
>                           `pushError` (couldNotFind (showName x))
>     -- `seek` find the local short name on our itinerary
>     -- go up while the guard fails, that is -- while the last name is not the
>     -- one we're looking for
>     seek :: (String, Int) -> ProofState ()
>     seek xn = goUp `whileA` (guard . (== xn) . last =<< getCurrentName)


> -- | Perform some action on the given entry. This leaves you back in the same
> --   place you started.
> withEntry :: Name -> (CurrentEntry -> CurrentEntry) -> ProofState ()
> withEntry name action = do
>     bookmark <- getCurrentName
>     goTo name
>     entry <- getCurrentEntry
>     putCurrentEntry (action entry)
>     goTo bookmark


> toggleEntryVisibility :: Name -> ProofState ()
> toggleEntryVisibility name = withEntry name $ \case
>     CModule name p meta -> CModule name p (meta & expanded %~ not)
>     CDefinition kind ref lastName tm anchor meta ->
>         CDefinition kind ref lastName tm anchor (meta & expanded %~ not)


> -- TODO(joel) - just lensify CurrentEntry
> -- TODO(joel) - name collision with TermController
> toggleEntryAnnotate :: Name -> ProofState ()
> toggleEntryAnnotate name = withEntry name $ \case
>     CModule name p meta -> CModule name p (meta & annotationExpanded %~ not)
>     CDefinition kind ref lastName tm anchor meta ->
>         CDefinition kind ref lastName tm anchor (meta & annotationExpanded %~ not)


Searching for a goal
--------------------

First off, a *goal* is a development which `Tip` is of the `Unknown`
type. Hence, to spot if the focus is set on a goal, we just have the
check the `Tip`.

> isGoal :: ProofState ()
> isGoal = do
>     devTip <- getDevTip
>     case devTip of
>         Unknown _ -> return ()
>         _ -> throwStack (errMsgStack "couldn't get dev tip"
>             :: StackError DInTmRN)

Let us start with some gymnastic. We implement `prevStep` and `nextStep`
that respectively looks for the previous and the next definition in the
proof context. By *previous*, we mean contained in an entry directly
above, or, if there is none, to the enclosing development. In other
words, it has been defined "just *previously*". The definition
transposes to the case of `nextStep`.

> prevStep :: ProofState ()
> prevStep =  (goUp >> much goIn) <|> goOut
>             `pushError`
>             (errMsgStack "prevStep: no previous steps."
>                 :: StackError DInTmRN)

> nextStep :: ProofState ()
> nextStep =  (goIn >> goTop) <|> goDown <|> (goOut `untilA` goDown)
>             `pushError`
>             (errMsgStack "nextStep: no more steps." :: StackError DInTmRN)

It is then straightforward to navigate relatively to goals: we move from
steps to steps, looking for a step that would be a goal.

> prevGoal :: ProofState ()
> prevGoal =  prevStep `untilA` isGoal
>             `pushError`
>             (errMsgStack "prevGoal: no previous goals."
>                 :: StackError DInTmRN)

> nextGoal :: ProofState ()
> nextGoal =  nextStep `untilA` isGoal
>             `pushError`
>             (errMsgStack "nextGoal: no more goals." :: StackError DInTmRN)

In the very spirit of a theorem prover, we sometimes want to stay at the
current location if it is a goal, and go to the next goal otherwise.

> seekGoal :: ProofState ()
> seekGoal = isGoal <|> nextGoal
