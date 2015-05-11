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

> import DisplayLang.Lexer
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
>
>             let err = stackItem
>                      [ errMsg "give: typechecking failed:"
>                      , errTm (DTIN tm)
>                      , errTm (DTIN tipTyTm)
>                      , errMsg "is not of type"
>                      , errTyVal (tipTy :<: SET)
>                      ] :: StackError DInTmRN
>
>             checkHere (tipTy :>: tm) `pushError` err
>
>             -- Lambda lift the given solution
>             globalScope <- getGlobalScope
>             above <- getEntriesAbove
>             let tmv = evTm $ parBind globalScope above tm
>             -- Update the entry as Defined, together with its definition
>             CDefinition kind (name := _ :<: ty) xn tyTm anchor meta
>                 <- getCurrentEntry
>             let ref = name := DEFN tmv :<: ty
>             putDevTip $ Defined tm $ tipTyTm :=>: tipTy
>             putCurrentEntry $
>                 CDefinition kind ref xn tyTm anchor meta
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
>     EDEF ref _ _ _ _ _ _ -> giveOutBelow $ NP ref
>     -- The entry was not a definition
>     _ -> throwDTmStr "done: entry above cursor must be a definition."


Slightly more sophisticated is the well-known `apply` tactic in Coq: we
are trying to solve a goal of type `T` while we have a definition of
type `Pi S T`. We can therefore solve the goal `T` provided we can solve
the goal `S`. We have this tactic too and, guess what, it is `apply`.

> apply :: ProofState (EXTM :=>: VAL)
> apply = getEntryAbove >>= apply'


> apply' :: Entry Bwd -> ProofState (EXTM :=>: VAL)
> apply' (EDEF f@(_ := _ :<: pi@(PI _ _)) _ _ _ _ _ _) = apply'' f pi
> apply' (EPARAM f@(_ := _ :<: pi@(PI _ _)) _ _ _ _ _) = apply'' f pi
> apply' _ =
>     throwDTmStr $ "apply: last entry in the development" ++
>                   " must be a definition with a pi-type."

 apply'' :: REF -> TY -> ProofState (EXTM :=>: VAL)
 apply'' ref pi@(PI from to) = do
     from' <- bquoteHere from
     pi' <- bquoteHere pi
     (holeTm :=>: _) <- make (AnchNo :<: from')
     give $ N $ (LRET (NP ref) :? pi') :$ A (N holeTm)

> apply'' :: REF -> TY -> ProofState (EXTM :=>: VAL)
> apply'' f (PI _S _T) = do
>     -- The entry above is a proof of `Pi S T`
>     -- Ask for a proof of `S`
>     _STm <- bquoteHere _S
>     sTm :=>: s <- make $ AnchStr "s" :<: _STm
>     -- Make a proof of `T`
>     _TTm <- bquoteHere $ _T Evidences.Eval.$$ A s
>     make $ AnchStr "t" :<: _TTm
>     goIn
>     -- give $ N $ (LRET (NP f) :? (C (Pi _STm _TTm))) :$ A (N sTm)
>     giveOutBelow $ N $ P f :$ A (N sTm)


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
> isParam (EPARAM _ _ _ _ _ _) = True
> isParam _ = False


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
>     t :=>: _ <- make (AnchRefine :<: ty)
>     cursorBottom
>     give (realiser t)
>     cursorTop
>     cursorDown
>     goIn

> prettyProofState :: ProofState String
> prettyProofState = do
>     inScope <- getInScope
>     me <- getCurrentName
>     d <- prettyPS inScope me
>     return (renderHouseStyle d)
>
> prettyPS :: Entries -> Name -> ProofState Doc
> prettyPS aus me = do
>         es <- replaceEntriesAbove B0
>         cs <- putBelowCursor F0
>         case (es, cs) of
>             (B0, F0)  -> prettyEmptyTip
>             _   -> do
>                 d <- prettyEs empty (es <>> F0)
>                 d' <- case cs of
>                     F0  -> return d
>                     _   -> do
>                         d'' <- prettyEs empty cs
>                         return (d Pretty.$$ text "---" Pretty.$$ d'')
>                 tip <- prettyTip
>                 putEntriesAbove es
>                 putBelowCursor cs
>                 return (lbrack <+> d' Pretty.$$ rbrack <+> tip)
>  where
>     prettyEs :: Doc -> Fwd (Entry Bwd) -> ProofState Doc
>     prettyEs d F0         = return d
>     prettyEs d (e :> es) = do
>         putEntryAbove e
>         ed <- prettyE e
>         prettyEs (d Pretty.$$ ed) es
>
>     prettyE (EPARAM (_ := DECL :<: ty) (x, _) k _ anchor _)  = do
>         ty' <- bquoteHere ty
>         tyd <- prettyHereAt (pred ArrSize) (SET :>: ty')
>         return (prettyBKind k
>                  (text x  <+> (brackets $ brackets $ text $ show anchor)
>                           <+> kword KwAsc
>                           <+> tyd))
>
>     prettyE e = do
>         goIn
>         d <- prettyPS aus me
>         goOut
>         return (sep  [  text (fst (entryLastName e))
>                         <+> (brackets $ brackets $ text $ show $ entryAnchor e)
>                      ,  nest 2 d <+> kword KwSemi
>                      ])
>
>     prettyEmptyTip :: ProofState Doc
>     prettyEmptyTip = do
>         tip <- getDevTip
>         case tip of
>             Module -> return (brackets empty)
>             _ -> do
>                 tip <- prettyTip
>                 return (kword KwDefn <+> tip)
>
>     prettyTip :: ProofState Doc
>     prettyTip = do
>         tip <- getDevTip
>         case tip of
>             Module -> return empty
>             Unknown (ty :=>: _) -> do
>                 hk <- getHoleKind
>                 tyd <- prettyHere (SET :>: ty)
>                 return (prettyHKind hk <+> kword KwAsc <+> tyd)
>             Suspended (ty :=>: _) prob -> do
>                 hk <- getHoleKind
>                 tyd <- prettyHere (SET :>: ty)
>                 return (text ("(SUSPENDED: " ++ show prob ++ ")")
>                             <+> prettyHKind hk <+> kword KwAsc <+> tyd)
>             Defined tm (ty :=>: tyv) -> do
>                 tyd <- prettyHere (SET :>: ty)
>                 tmd <- prettyHereAt (pred ArrSize) (tyv :>: tm)
>                 return (tmd <+> kword KwAsc <+> tyd)
>
>     prettyHKind :: HKind -> Doc
>     prettyHKind Waiting     = text "?"
>     prettyHKind Hoping      = text "HOPE?"
>     prettyHKind (Crying s)  = text ("CRY <<" ++ s ++ ">>")
>
