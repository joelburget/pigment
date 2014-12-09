\section{Labelled Types}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Labelled where

%endif


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


