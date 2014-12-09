\section{Anchors}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Anchor where

%endif


> import -> DistillRules where
>   distill es (ANCHORS :>: x@(ANCHOR (TAG u) t ts)) = do
>     (displayTs :=>: _) <- distill es (ALLOWEDBY (evTm t) :>: ts)
>     return (DANCHOR u displayTs :=>: evTm x)


