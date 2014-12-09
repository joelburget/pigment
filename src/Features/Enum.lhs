\section{Enum}
\label{sec:Features.Enum}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Enum where

%endif





Conversely, we can distill an index to a tag as follows. Note that if the
index contains a stuck term, we simply give up and let the normal distillation
rules take over; the pretty-printer will then do the right thing.

> import -> DistillRules where
>   distill _ (ENUMT t :>: tm) | Just r <- findIndex (t :>: tm) = return r
>     where
>       findIndex :: (VAL :>: INTM) -> Maybe (DInTmRN :=>: VAL)
>       findIndex (CONSE (TAG s)  _ :>: ZE)    = Just (DTAG s :=>: evTm tm)
>       findIndex (CONSE _        a :>: SU b)  = findIndex (a :>: b)
>       findIndex _                            = Nothing

Since elaboration turns lists into functions from enumerated types, we can
do the reverse when distilling. This is slightly dubious.

>   distill es (PI (ENUMT e) t :>: L (x :. N (op :@ [e', NV 0, t', b])))
>     | op == switchOp = distill es (branchesOp @@ [e, t] :>: b)
