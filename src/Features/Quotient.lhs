\section{Quotients}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Quotient where

%endif

|equivalenceRelation A R| is the proposition that |R| is an equivalence
relation over |A|.

> import -> Coerce where
>   coerce (Quotient (_X, _Y) _ _) q (CLASS x) = Right $
>     CLASS (coe @@ [_X, _Y, CON $ q $$ Fst, x])


> import -> KeywordConstructors where
>   KwQuotient  :: Keyword

> import -> KeywordTable where
>   key KwQuotient  = "Quotient"

> import -> DInTmParsersSpecial where
>   (AndSize, (|DQUOTIENT (%keyword KwQuotient%) (sizedDInTm ArgSize) (sizedDInTm ArgSize) (sizedDInTm ArgSize)|)) :


As a bit of syntactic sugar, we elaborate |con| as |COMPOSITE| and |[x]| as
|CLASS x|. \question{Why not just use |CON| rather than |COMPOSITE| everywhere?}

> import -> MakeElabRules where
>   makeElab' loc (MONAD d x :>: DCON t) =
>     makeElab' loc (MONAD d x :>: DCOMPOSITE t)
>   makeElab' loc (QUOTIENT a r p :>: DPAIR x DVOID) =
>     makeElab' loc (QUOTIENT a r p :>: DCLASS x)
