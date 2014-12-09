\section{Nu}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Nu where

%endif






> import -> MakeElabRules where
>     makeElab' loc (NU l d :>: DVOID) =
>         makeElab' loc (NU l d :>: DCON (DPAIR DZE DVOID))
>     makeElab' loc (NU l d :>: DPAIR s t) =
>         makeElab' loc (NU l d :>: DCON (DPAIR (DSU DZE) (DPAIR s (DPAIR t DVOID))))
>     makeElab' loc (SET :>: DNU Nothing d) = do
>         lt :=>: lv <- eFaker
>         dt :=>: dv <- subElab loc (desc :>: d)
>         return $ NU (Just (N lt)) dt :=>: NU (Just lv) dv
>     makeElab' loc (NU l d :>: DCOIT DU sty f s) = do
>       d' :=>: _ <- eQuote d
>       makeElab' loc (NU l d :>: DCOIT (DTIN d') sty f s)



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
