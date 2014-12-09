\section{Labelled Types}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Labelled where

%endif




\question{The following is all commented out. Is it detritus?}

<   canTy chev (ty :>: Call c tm) = do
<      tytv@(ty :=>: tyv) <- chev (SET :>: ty)
<      ccv@(c :=>: cv) <- chev (ty :>: c)
<      tmtv@(tm :=>: tmv) <- chev (LABEL cv ty :>: tm)
<      return (Call ccv tmtv)


