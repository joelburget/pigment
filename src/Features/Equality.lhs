\section{Equality}
\label{sec:Features.Equality}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Equality where

%endif


In the display syntax, a blue equality can be between arbitrary DExTms,
rather than ascriptions. To allow this, we add a suitable constructor |DEqBlue|
to DInTm, along with appropriate elaboration and distillation rules.




> import -> DistillRules where
>   distill es (PROP :>: tm@(EQBLUE (tty :>: t) (uty :>: u))) = do
>       t' <- toDExTm es (tty :>: t)
>       u' <- toDExTm es (uty :>: u)
>       return $ DEqBlue t' u' :=>: evTm tm

When distilling a proof of an equation, we first check to see if the equation
holds definitionally. If so, we avoid forcing the proof and return refl instead.

>   distill es (p@(PRF (EQBLUE (_S :>: s) (_T :>: t))) :>: q) = do
>       r <- askNSupply
>       if equal (SET :>: (_S, _T)) r && equal (_S :>: (s, t)) r
>           then return (DU :=>: N (P refl :$ A _S :$ A s))
>           else distillBase es (p :>: q)
