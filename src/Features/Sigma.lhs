\section{Sigma}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Sigma where

%endif








> import -> DistillRules where
>   distill es (UNIT :>: _) = return $ DVOID :=>: VOID
