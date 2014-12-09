\section{Records feature}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Record where

%endif



\subsection{Extending the concrete syntax}


> import -> DInTmParsersSpecial where
>   (AndSize, (|(DRECORD Nothing) (%keyword KwRecord%) (sizedDInTm ArgSize)|)) :
>   (ArgSize, (|(DRSIG) (%keyword KwRSig%) |)) :
>   (ArgSize, (|(DREMPTY) (%keyword KwREmpty%)|)) :
>   (ArgSize, (|(DRCONS) (%keyword KwRCons%) (sizedDInTm ArgSize) (sizedDInTm ArgSize) (sizedDInTm ArgSize)|)) :
