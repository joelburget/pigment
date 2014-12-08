\section{Labelled Types}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Labelled where

%endif

> import -> Coerce where
>   coerce (Label (l1, l2) (t1, t2)) q (LRET t) =
>       Right $ LRET $ coe @@ [t1, t2, CON (q $$ Snd), t]


> import -> KeywordConstructors where
>   KwCall      :: Keyword
>   KwLabel     :: Keyword
>   KwLabelEnd  :: Keyword
>   KwRet       :: Keyword

> import -> KeywordTable where
>   key KwCall      = "call"
>   key KwLabel     = "<"
>   key KwLabelEnd  = ">"
>   key KwRet       = "return"  -- rename me

> import -> ElimParsers where
>   (AppSize, (| Call (%keyword KwCall%) ~DU |)) :

> import -> DInTmParsersSpecial where
>   (ArgSize, (|DLABEL (%keyword KwLabel%) (sizedDInTm AppSize) (%keyword KwAsc%) (sizedDInTm ArgSize) (%keyword KwLabelEnd%)|)) :
>   (ArgSize, (|DLRET (%keyword KwRet%) (sizedDInTm ArgSize)|)) :


If we spot a neutral term being called when distilling, we distill the label
instead, thereby replacing horrible stuck inductions with the pretty functions
they implement.

> import -> DistillInferRules where
>   distillInfer es (t :$ Call (N l)) as = distillInfer es l as


\question{The following is all commented out. Is it detritus?}

<   canTy chev (ty :>: Call c tm) = do
<      tytv@(ty :=>: tyv) <- chev (SET :>: ty)
<      ccv@(c :=>: cv) <- chev (ty :>: c)
<      tmtv@(tm :=>: tmv) <- chev (LABEL cv ty :>: tm)
<      return (Call ccv tmtv)


< import -> OpCompile where
<   ("call", [ty, l, t]) -> l

