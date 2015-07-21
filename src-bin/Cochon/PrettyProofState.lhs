> {-# LANGUAGE PatternSynonyms #-}

> module Cochon.PrettyProofState where

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
> import DisplayLang.Lexer
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
>         tyd <- prettyHereAt (pred ArrSize) (SET :>: ty)
>         return (prettyBKind k
>                  (text x  <+> (showAnchor anchor)
>                           <+> kword KwAsc
>                           <+> tyd))
>
>     prettyE e = do
>         goIn
>         d <- prettyPS aus me
>         goOut
>         return (sep  [  text (fst (entryLastName e))
>                         <+> (showAnchor $ entryAnchor e)
>                      ,  nest 2 d <+> kword KwSemi
>                      ])
>
>     showAnchor :: EntityAnchor -> Doc
>     showAnchor (AnchStr str) = brackets $ brackets $ text str
>     showAnchor _ = empty
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
