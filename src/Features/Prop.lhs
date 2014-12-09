\section{Prop}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Prop where

%endif


Elim forms inherited from elsewhere




> import -> DInTmParsersMore where
>   (AndSize, \ s -> (| (DAND s) (%keyword KwAnd%) (sizedDInTm AndSize)  |)) :
>   (ArrSize, \ s -> (| (DIMP s) (%keyword KwImp%) (sizedDInTm PiSize)   |)) :



> import -> DistillRules where
>   distill es (PRF TRIVIAL :>: _) = return (DU :=>: VOID)
