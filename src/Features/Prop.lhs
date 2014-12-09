\section{Prop}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Prop where

%endif


Elim forms inherited from elsewhere






> import -> DistillRules where
>   distill es (PRF TRIVIAL :>: _) = return (DU :=>: VOID)
