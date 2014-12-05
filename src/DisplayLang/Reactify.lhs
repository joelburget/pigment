\section{Pretty-printing}
\label{sec:DisplayLang.Reactify}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE ScopedTypeVariables, GADTs, FlexibleInstances, TypeOperators,
>     TypeSynonymInstances #-}

> module DisplayLang.Reactify where

> import Data.List
> import Text.PrettyPrint.HughesPJ

> import ProofState.Structure.Developments

> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.Scheme
> import DisplayLang.Lexer

> import Features.Features ()

> import Evidences.Tm

> import Kit.BwdFwd
> import Kit.MissingLibrary hiding ((<+>))

%endif

The |reactKword| function gives a react element representing a |Keyword|.

> reactKword :: Keyword -> ReactM ()
> reactKword = fromString . key

The |Reactive| class describes things that can be made into React elements.

> class Reactive x where
>     reactify :: x -> ReactM ()

> instance Reactive (Can DInTmRN) where
>     reactify Set       = reactKword KwSet
>     reactify (Pi s t)  = reactPi empty (DPI s t)
>     reactify (Con x)   = reactKword KwCon >> reactify x
>     import <- CanReactive
>     reactify can       = fromString . show $ can

The |reactPi| function takes a term and the current size. It accumulates
domains until a non(dependent) $\Pi$-type is found, then calls |reactPiMore|
to produce the final element.

> reactPi :: DInTmRN -> Size -> Doc
> reactPi (DPI s (DL (DK t))) = reactPiMore bs
>     (reactify s (pred PiSize) >> reactKword KwArr >> reactify t PiSize)
> reactPi (DPI s (DL (x ::. t))) =
>     reactPi (bs <> parens (fromString x >> reactKword KwAsc >> reactify s maxBound)) t
> reactPi (DPI s t) = reactPiMore bs
>     (reactKword KwPi >> reactify s minBound >> reactify t minBound)
> reactPi tm = reactPiMore bs (reactify tm PiSize)

The |reactPiMore| function takes a bunch of domains (which may be empty)
and a codomain, and represents them appropriately for the current size.

> reactPiMore :: Doc -> Doc -> Size -> Doc
> reactPiMore bs d
>   | isEmpty bs  = wrapDoc d PiSize
>   | otherwise   = wrapDoc (bs >> reactKword KwArr >> d) PiSize


The |Elim| functor is straightforward.

> instance Reactive (Elim DInTmRN) where
>     reactify (A t)  = reactify t
>     reactify Out    = reactKword KwOut)
>     import <- ElimReactive
>     reactify elim   = fromString $ show $ elim


To reactify a scope, we accumulate arguments until something other
than a $\lambda$-term is reached.

> instance Reactive DSCOPE where
>     reactify s = reactLambda (B0 :< dScopeName s) (dScopeTm s)

> reactLambda :: Bwd String -> DInTmRN -> Size -> ReactM ()
> reactLambda vs (DL s) = reactLambda (vs :< dScopeName s) (dScopeTm s)
> reactLambda vs tm = do
>     reactKword KwLambda
>     fromString (intercalate " " (trail vs))
>     reactKword KwArr
>     reactify tm


> instance Reactive DInTmRN where
>     reactify (DL s)          = reactify s
>     reactify (DC c)          = reactify c
>     reactify (DN n)          = reactify n
>     reactify (DQ x)          = fromString $ '?':text x
>     reactify DU              = reactKword KwUnderscore
>     import <- DInTmReactive
>     reactify indtm           = fromString $ show $ indtm


> instance Reactive DExTmRN where
>     reactify (n ::$ els)  = reactify n >> map reactify els

> instance Reactive DHEAD where
>     reactify (DP x)       = fromSrring (showRelName x)
>     reactify (DType ty)   = reactKword KwAsc >> reactify ty
>     reactify (DTEx ex)    = fromString $ show ex

> instance Reactive (Scheme DInTmRN) where
>     reactify (SchType ty) = reactKword KwAsc >> reactify ty
>     reactify (SchExplicitPi (x :<: schS) schT) = do
>         parens (fromString x >> reactify schS)
>         reactify schT
>     reactify (SchImplicitPi (x :<: s) schT) = do
>         braces (fromString x >> reactKword KwAsc >> reactify s)
>         reactify schT

> import <- Reactive


The |reactBKind| function reactifies a |ParamKind| if supplied
with an element representing its name and type.

> reactBKind :: ParamKind -> ReactM () -> ReactM ()
> reactBKind ParamLam  d = reactKword KwLambda >> d >> reactKword KwArr
> reactBKind ParamAll  d = reactKword KwLambda >> d >> reactKword KwImp
> reactBKind ParamPi   d = parens d >> reactKword KwArr