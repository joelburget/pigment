\section{FreeMonad}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.FreeMonad where

%endif

\question{What should the coercion rule be for |COMPOSITE|?}


> import -> DInTmParsersSpecial where
>   (ArgSize, (|DRETURN (%keyword KwReturn%) (sizedDInTm ArgSize)|)) :
>   (AndSize, (|DMONAD (%keyword KwMonad%) (sizedDInTm ArgSize) (sizedDInTm ArgSize)|)) :
