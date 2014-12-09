\section{Nu}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Nu where

%endif








To avoid an infinite loop when distilling, we have to be a little cleverer
and call canTy directly rather than letting distill do it for us.

> import -> DistillRules where
>     distill _ (NU _ _ :>: CON (PAIR ZE VOID)) =
>         return (DVOID :=>: CON (PAIR ZE VOID))
>     distill es (C ty@(Nu _) :>: C c@(Con (PAIR (SU ZE) (PAIR _ (PAIR _ VOID))))) = do
>         Con (DPAIR _ (DPAIR s (DPAIR t _)) :=>: v) <- canTy (distill es) (ty :>: c)
>         return (DPAIR s t :=>: CON v)


If a label is not in scope, we remove it, so the definition appears at the
appropriate place when the proof state is printed.

>     distill es (SET :>: tm@(C (Nu ltm@(Just _ :?=: _)))) = do
>       cc <- canTy (distill es) (Set :>: Nu ltm)
>       return ((DC $ fmap termOf cc) :=>: evTm tm)
