\section{Pretty-printing}
\label{sec:DisplayLang.Reactify}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE ScopedTypeVariables, GADTs, FlexibleInstances, TypeOperators,
>     TypeSynonymInstances, OverloadedStrings #-}

> module DisplayLang.Reactify where

> import Data.List
> import Data.String (fromString)

import Text.PrettyPrint.HughesPJ

> import ProofState.Structure.Developments

> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.Scheme
> import DisplayLang.Lexer

> import Features.Features ()

> import Evidences.Tm

> import Kit.BwdFwd
> import Kit.MissingLibrary hiding ((<+>))

> import React hiding (key)

%endif

The |reactKword| function gives a react element representing a |Keyword|.

> reactKword :: Keyword -> PureReact
> reactKword = fromString . key

> parens :: PureReact -> PureReact
> parens r = "(" >> r >> ")"

The |Reactive| class describes things that can be made into React elements.

> class Reactive x where
>     reactify :: x -> PureReact

> instance Reactive (Can DInTmRN) where
>     reactify Set       = reactKword KwSet
>     reactify (Pi s t)  = reactPi "" (DPI s t)
>     reactify (Con x)   = reactKword KwCon >> reactify x
>     import <- CanReactive
>     reactify can       = fromString . show $ can

The |reactPi| function takes a term and the current size. It accumulates
domains until a non(dependent) $\Pi$-type is found, then calls |reactPiMore|
to produce the final element.

> reactPi :: PureReact -> DInTmRN -> PureReact
> reactPi bs (DPI s (DL (DK t))) = reactPiMore bs
>     -- (reactify s >> reactKword KwArr >> reactify t) XXX
>     (reactKword KwArr)
> reactPi bs (DPI s (DL (x ::. t))) =
>     -- reactPi (bs >> "(" >> (fromString x >> reactKword KwAsc >> reactify s) >> ")") t XXX
>     reactPi (bs >> "(" >> (fromString x >> reactKword KwAsc) >> ")") t
> reactPi bs (DPI s t) = reactPiMore bs
>     -- (reactKword KwPi >> reactify s >> reactify t) XXX
>     (reactKword KwPi)
> -- reactPi bs tm = reactPiMore bs (reactify tm) XXX
> reactPi bs tm = ""

The |reactPiMore| function takes a bunch of domains (which may be empty)
and a codomain, and represents them appropriately for the current size.

> reactPiMore :: PureReact -> PureReact -> PureReact
> reactPiMore bs d = bs >> reactKword KwArr >> d

-- >   | isEmpty bs  = wrapDoc d PiSize
-- >   | otherwise   = wrapDoc (bs >> reactKword KwArr >> d) PiSize



To reactify a scope, we accumulate arguments until something other
than a $\lambda$-term is reached.

> instance Reactive DSCOPE where
>     reactify s = reactLambda (B0 :< dScopeName s) (dScopeTm s)

> reactLambda :: Bwd String -> DInTmRN -> PureReact
> reactLambda vs (DL s) = reactLambda (vs :< dScopeName s) (dScopeTm s)
> reactLambda vs tm = do
>     reactKword KwLambda
>     fromString $ intercalate " " $ trail vs
>     reactKword KwArr
>     reactify tm


> instance Reactive DInTmRN where
>     reactify (DL s)          = reactify s
>     reactify (DC c)          = reactify c
>     reactify (DN n)          = reactify n
>     reactify (DQ x)          = fromString $ '?':x
>     reactify DU              = reactKword KwUnderscore
>     import <- DInTmReactive
>     reactify indtm           = fromString $ show $ indtm


> instance Reactive DExTmRN where
>     reactify (n ::$ els)  = reactify n >> mapM_ reactify els

> instance Reactive DHEAD where
>     reactify (DP x)       = fromString (showRelName x)
>     reactify (DType ty)   = reactKword KwAsc >> reactify ty
>     reactify (DTEx ex)    = fromString $ show ex

> instance Reactive (Scheme DInTmRN) where
>     reactify (SchType ty) = reactKword KwAsc >> reactify ty
>     reactify (SchExplicitPi (x :<: schS) schT) = do
>         "(" >> fromString x >> reactify schS >> ")"
>         reactify schT
>     reactify (SchImplicitPi (x :<: s) schT) = do
>         "[" >> fromString x >> reactKword KwAsc >> reactify s >> "]"
>         reactify schT

> import <- Reactive

The |Elim| functor is straightforward.

> instance Reactive (Elim DInTmRN) where
>     reactify (A t)  = reactify t
>     reactify Out    = reactKword KwOut)
>     import <- ElimReactive
>     reactify elim   = fromString $ show $ elim
