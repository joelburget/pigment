Solving goals
=============

> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes, PatternSynonyms, NamedFieldPuns #-}

> module ProofState.Interface.Solving where

> import Control.Applicative hiding (empty)
> import Control.Monad
> import qualified Data.Foldable as Foldable

> import Control.Error

> import Kit.BwdFwd
> import Kit.MissingLibrary
> import ProofState.Structure.Developments
> import ProofState.Edition.ProofContext
> import ProofState.Edition.Scope
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation
> import ProofState.Interface.Lifting
> import ProofState.Interface.Search
> import ProofState.Interface.ProofKit
> import ProofState.Interface.Definition
> import ProofState.Interface.Parameter
> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import Evidences.Tm
> import Evidences.Eval
> import Elaboration.Wire

> import ProofState.Structure.Entries

> import Kit.Trace
> import DisplayLang.PrettyPrint
> import Text.PrettyPrint.HughesPJ as Pretty
> import Distillation.Distiller
> import NameSupply.NameSupply

Giving a solution
-----------------

The `give` command takes a term and solves the current goal with it, if
it type-checks. At the end of the operation, the cursor has not moved:
we are still under the goal, which has now been `Defined`. Note that
entries below the cursor are (lazily) notified of the good news.

> give :: INTM -> ProofState (EXTM :=>: VAL)
> give tm = do
>     tip <- getDevTip
>     case tip of
>         Unknown (tipTyTm :=>: tipTy) -> do
>             -- Working on a goal
>             -- The `tm` is of the expected type
>             checkHere (tipTy :>: tm)
>                 `pushError`
>                 (stackItem
>                      [ errMsg "give: typechecking failed:"
>                      , errTm (DTIN tm)
>                      , errTm (DTIN tipTyTm)
>                      , errMsg "is not of type"
>                      , errTyVal (tipTy :<: SET)
>                      ] :: StackError DInTmRN
>                 )
>
>             -- Lambda lift the given solution
>             globalScope <- getGlobalScope
>             above <- getEntriesAbove
>             let tmv = evTm $ parBind globalScope above tm
>             -- Update the entry as Defined, together with its definition
>             CDefinition kind (name := _ :<: ty) xn tyTm meta
>                 <- getCurrentEntry
>             let ref = name := DEFN tmv :<: ty
>             putDevTip $ Defined tm $ tipTyTm :=>: tipTy
>             putCurrentEntry $ CDefinition kind ref xn tyTm meta
>             -- Propagate the good news
>             updateRef ref
>             -- Return the reference
>             return $ applySpine ref globalScope
>         _  -> throwDTmStr "give: only possible for incomplete goals."

For convenience, we combine giving a solution and moving. Indeed, after
`give`, the cursor stands in a rather boring position: under a `Defined`
entry, with no work to do. So, a first variant is `giveOutBelow` that
gives a solution and moves just below the now-defined entry. A second
variant is `giveNext` that gives as well and moves to the next goal, if
one is available.

> giveOutBelow :: INTM -> ProofState (EXTM :=>: VAL)
> giveOutBelow tm = give tm <* goOutBelow

> giveNext :: INTM -> ProofState (EXTM :=>: VAL)
> giveNext tm = give tm <* (nextGoal <|> goOut)

Finding trivial solutions
-------------------------

Often, to solve a goal, we make a definition that contains further
developments and, eventually, leads to a solution. To solve the goal, we
are therefore left to `give` this definition. This is the role of the
`done` command that tries to `give` the entry above the cursor.

> done :: ProofState (EXTM :=>: VAL)
> done = do
>   devEntry <- getEntryAbove
>   case devEntry of
>     -- The entry above is indeed a definition
>     EDEF ref _ _ _ _ _ -> giveOutBelow $ NP ref
>     -- The entry was not a definition
>     _ -> throwDTmStr "done: entry above cursor must be a definition."


Slightly more sophisticated is the well-known `apply` tactic in Coq: we
are trying to solve a goal of type `T` while we have a definition of
type `Pi S T`. We can therefore solve the goal `T` provided we can solve
the goal `S`. We have this tactic too and, guess what, it is `apply`.

> apply :: ProofState (EXTM :=>: VAL)
> apply = getEntryAbove >>= apply'


> apply' :: Entry Bwd -> ProofState (EXTM :=>: VAL)
> apply' (EDEF f@(_ := _ :<: pi@(PI _ _)) _ _ _ _ _) = apply'' f pi
> apply' (EPARAM f@(_ := _ :<: pi@(PI _ _)) _ _ _ _) = apply'' f pi
> apply' _ = do
>     elabTrace "elab' fail :("
>     throwDTmStr $ "apply: last entry in the development" ++
>                   " must be a definition with a pi-type."

 apply'' :: REF -> TY -> ProofState (EXTM :=>: VAL)
 apply'' ref pi@(PI from to) = do
     (holeTm :=>: _) <- make (AnchNo :<: from)
     give $ N $ (LRET (NP ref) :? pi) :$ A (N holeTm)

> apply'' :: REF -> TY -> ProofState (EXTM :=>: VAL)
> apply'' f (PI _S _T) = do
>     elabTrace $ "apply' success!"
>     -- The entry above is a proof of `Pi S T`
>     -- Ask for a proof of `S`
>     sTm :=>: s <- make $ "s" :<: _S
>     -- Make a proof of `T`
>     let _TTm = _T Evidences.Eval.$$ A s
>     make $ "t" :<: _TTm
>     goIn
>     -- give $ N $ (LRET (NP f) :? (C (Pi _S _TTm))) :$ A (N sTm)
>     giveOutBelow $ N $ P f :$ A (N sTm)


The tactic auto works as follows. It first tries to call reflexivity and
assumption. If one of these calls solves the goal, the job is done. Otherwise
auto tries to apply the most recently introduced assumption that can be applied
to the goal without producing and error. This application produces subgoals.
There are two possible cases. If the sugboals produced can be solved by a
recursive call to auto, then the job is done. Otherwise, if this application
produces at least one subgoal that auto cannot solve, then auto starts over by
trying to apply the second most recently introduced assumption. It continues in
a similar fashion until it finds a proof or until no assumption remains to be
tried.


> focuses :: [a] -> [([a], a, [a])]
> focuses []     = []
> focuses (a:as) = ([], a, as):(map helper (focuses as))
>     where helper (pres, focus, post) = ((a:pres), focus, post)


> focuses' :: [a] -> [(a, [a])]
> focuses' = map helper . focuses
>     where helper (pres, focus, post) = (focus, pres ++ post)

> notFound = throwDTmStr "no valid parameter found"

> auto :: ProofState ()
> auto = do
>     entries <- getInScope
>     let entryList = filter isParam $ Foldable.toList entries
>     autoSpreader 5 entryList

> autoSpreader :: Int -> [Entry Bwd] -> ProofState ()
> autoSpreader n entries = do
>     let autoWith (x, xs) = auto' n (x:xs)
>         subattempts = map autoWith (focuses' entries)
>     elabTrace $ show (length entries) ++ " entries in scope"
>     elabTrace $ show (length subattempts) ++ " subattempts"
>     void done <|> (assumption <|> foldl (<|>) notFound subattempts)

> typeof :: Entry Bwd -> Maybe TY
> typeof (EDEF (_ := _ :<: ty) _ _ _ _ _) = Just ty
> typeof (EPARAM (_ := _ :<: ty) _ _ _ _) = Just ty
> typeof _ = Nothing

> auto' :: Int -> [Entry Bwd] -> ProofState ()
> -- TODO(joel) figure out how to ensure this is shown if it happens! Don't
> -- want it to be overwritten by an uninteresting shallower error.
> auto' 0 _ = throwDTmStr "auto bottomed out!"
> auto' _ [] = throwDTmStr "no valid parameter found"
> auto' n (entry:entries) = do
>     elabTrace $ "auto' " ++ (fst (last (entryName entry)))
>     elabTrace $ "type: " ++ show (typeof entry)
>     apply' entry
>     autoSpreader (n-1) entries

matchesGoal :: NameSupply -> INTM -> Maybe (INTM :=>: TY) -> Bool
matchesGoal _ _ Nothing = False
matchesGoal ns tm (Just (_ :=>: ty)) =
    let ch = check (ty :>: tm)
        result = typeCheck ch ns
    in isRight result

The `ungawa` command looks for a truly obvious thing to do, and does it.

> ungawa :: ProofState ()
> ungawa =  void done <|> void apply <|> void (lambdaParam "ug")
>           `pushError` (errMsgStack "ungawa: no can do." :: StackError DInTmRN)


> isParam :: Entry Bwd -> Bool
> isParam (EPARAM _ _ _ _ _) = True
> isParam _ = False


> assumption :: ProofState ()
> assumption = do
>     entries <- getInScope
>     -- Try just returning the entry
>     let f (EPARAM ref _ _ term _) = void $
>             let justTm :: INTM
>                 justTm = NP ref
>             in elabTrace ("giving " ++ show justTm) >> give (LRET justTm)
>         f _ = notFound
>     -- ... for each entry
>     foldl (<|>) notFound (map f (Foldable.toList entries))


Refining the proof state
------------------------

To refine the proof state, we must supply a new goal type and a
realiser, which takes values in the new type to values in the original
type. The `refineProofState` command creates a new subgoal at the top of
the working development, so the entries in that development are not in
scope.

> refineProofState :: INTM -> (EXTM -> INTM) -> ProofState ()
> refineProofState ty realiser = do
>     cursorTop
>     t :=>: _ <- make ("refine" :<: ty)
>     cursorBottom
>     give (realiser t)
>     cursorTop
>     cursorDown
>     goIn
