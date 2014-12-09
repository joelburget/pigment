\section{Prop}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Prop where

%endif


Elim forms inherited from elsewhere




> import -> DInTmParsersSpecial where
>   (ArgSize, (|DPROP     (%keyword KwProp%)|)) :
>   (ArgSize, (|DABSURD   (%keyword KwAbsurd%)|)) :
>   (ArgSize, (|DTRIVIAL  (%keyword KwTrivial%)|)) :
>   (AndSize, (|DPRF      (%keyword KwPrf%) (sizedDInTm AndSize)|)) :
>   (AndSize, (|DINH      (%keyword KwInh%) (sizedDInTm ArgSize)|)) :
>   (AndSize, (|DWIT      (%keyword KwWit%) (sizedDInTm ArgSize)|)) :
>   (AndSize, (|DALL      (%keyword KwAll%) (sizedDInTm ArgSize) (sizedDInTm ArgSize)|)) :

> import -> DInTmParsersMore where
>   (AndSize, \ s -> (| (DAND s) (%keyword KwAnd%) (sizedDInTm AndSize)  |)) :
>   (ArrSize, \ s -> (| (DIMP s) (%keyword KwImp%) (sizedDInTm PiSize)   |)) :



> import -> DistillRules where
>   distill es (PRF TRIVIAL :>: _) = return (DU :=>: VOID)
