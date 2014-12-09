\section{Anchors}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Anchor where

%endif


> import -> DInTmTraverse where
>   traverseDTIN f (DAnchor s args) = (|(DAnchor s) (traverseDTIN f args)|)

> import -> DInTmPretty where
>   pretty (DANCHOR s args)  = wrapDoc (text s <+> pretty args ArgSize) ArgSize

> import -> DistillRules where
>   distill es (ANCHORS :>: x@(ANCHOR (TAG u) t ts)) = do
>     (displayTs :=>: _) <- distill es (ALLOWEDBY (evTm t) :>: ts)
>     return (DANCHOR u displayTs :=>: evTm x)


