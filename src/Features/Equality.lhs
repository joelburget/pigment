\section{Equality}
\label{sec:Features.Equality}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Equality where

%endif


In the display syntax, a blue equality can be between arbitrary DExTms,
rather than ascriptions. To allow this, we add a suitable constructor |DEqBlue|
to DInTm, along with appropriate elaboration and distillation rules.

> import -> DInTmPretty where
>   pretty (DEqBlue t u) = wrapDoc
>       (pretty t ArgSize <+> kword KwEqBlue <+> pretty u ArgSize)
>       ArgSize

> import -> DInTmReactive where
>   reactify (DEqBlue t u) = reactify t >> kword KwEqBlue >> reactify u

> import -> DInTmTraverse where
>   traverseDTIN f (DEqBlue t u) =
>     (| DEqBlue (traverseDTEX f t) (traverseDTEX f u) |)


> import -> KeywordConstructors where
>   KwEqBlue :: Keyword

> import -> KeywordTable where
>   key KwEqBlue = "=="

> import -> DInTmParsersMore where
>   (EqSize, \ t -> (| DEqBlue  (pFilter isEx (pure t)) (%keyword KwEqBlue%)
>                               (pFilter isEx (sizedDInTm (pred EqSize))) |)) :

> import -> ParserCode where
>   isEx :: DInTmRN -> Maybe DExTmRN
>   isEx (DN tm)  = Just tm
>   isEx _        = Nothing


> import -> MakeElabRules where
>   makeElab' loc (PROP :>: DEqBlue t u) = do
>       ttt <- subElabInfer loc t
>       utt <- subElabInfer loc u
>       let ttm :=>: tv :<: tty :=>: ttyv = extractNeutral ttt
>       let utm :=>: uv :<: uty :=>: utyv = extractNeutral utt
>       return $  EQBLUE (tty   :>: ttm)  (uty   :>: utm)
>           :=>:  EQBLUE (ttyv  :>: tv)   (utyv  :>: uv)

> import -> DistillRules where
>   distill es (PROP :>: tm@(EQBLUE (tty :>: t) (uty :>: u))) = do
>       t' <- toDExTm es (tty :>: t)
>       u' <- toDExTm es (uty :>: u)
>       return $ DEqBlue t' u' :=>: evTm tm

When distilling a proof of an equation, we first check to see if the equation
holds definitionally. If so, we avoid forcing the proof and return refl instead.

>   distill es (p@(PRF (EQBLUE (_S :>: s) (_T :>: t))) :>: q) = do
>       r <- askNSupply
>       if equal (SET :>: (_S, _T)) r && equal (_S :>: (s, t)) r
>           then return (DU :=>: N (P refl :$ A _S :$ A s))
>           else distillBase es (p :>: q)
