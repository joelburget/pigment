\section{Anchors}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Anchor where

%endif


\subsection{Plugging in canonical forms}

> import -> CanTraverse where
>     traverse _ Anchors = (| Anchors |)
>     traverse f (Anchor u t ts) = (|Anchor (f u) (f t) (f ts)|)
>     traverse f (AllowedBy t) = (|AllowedBy (f t)|)
>     traverse f AllowedEpsilon = (|AllowedEpsilon|)
>     traverse f (AllowedCons _S _T q s ts) = (|AllowedCons (f _S) (f _T) (f q) (f s) (f ts)|)

> import -> CanHalfZip where
>     halfZip Anchors Anchors = Just Anchors
>     halfZip (Anchor u1 t1 ts1) (Anchor u2 t2 ts2) = Just $ Anchor (u1, u2) (t1, t2) (ts1, ts2)
>     halfZip (AllowedBy t1) (AllowedBy t2) = Just $ AllowedBy (t1, t2)
>     halfZip AllowedEpsilon AllowedEpsilon = Just $ AllowedEpsilon
>     halfZip (AllowedCons _S1 _T1 q1 s1 ts1) (AllowedCons _S2 _T2 q2 s2 ts2) = Just $ AllowedCons (_S1, _S2) (_T1, _T2) (q1, q2) (s1, s2) (ts1, ts2)

\subsection{Plugging in eliminators}

> import -> ElimTyRules where
>     {- empty -}

> import -> ElimComputation where
>     {- empty -}

> import -> ElimCompile where
>     {- empty -}

> import -> ElimTraverse where
>     {- empty -}

> import -> ElimPretty where
>     {- empty -}

\subsection{Plugging in operators}

> import -> Operators where
>     {- empty -}

> import -> OpCompile where
>     {- empty -}

> import -> OpCode where
>     {- empty -}

\subsection{Plugging in axioms and primitives}

> import -> RulesCode where
>     {- empty -}

> import -> Primitives where

\subsection{Extending the type-checker}

> import -> Check where
>     {- mepty -}

\subsection{Extending the equality}

> import -> OpRunEqGreen where

> import -> Coerce where

\subsection{Extending the display language}

> import -> DInTmConstructors where
>   DAnchor :: String -> DInTm p x -> DInTm p x

> import -> DInTmTraverse where
>   traverseDTIN f (DAnchor s args) = (|(DAnchor s) (traverseDTIN f args)|)

> import -> DInTmPretty where
>   pretty (DANCHOR s args)  = wrapDoc (text s <+> pretty args ArgSize) ArgSize

> import -> Pretty where

\subsection{Extending the concrete syntax}

> import -> KeywordConstructors where

> import -> KeywordTable where

> import -> ElimParsers where

> import -> DInTmParsersSpecial where

> import -> DInTmParsersMore where

> import -> ParserCode where

\subsection{Extending the elaborator and distiller}

> import -> MakeElabRules where

> import -> DistillRules where
>   distill es (ANCHORS :>: x@(ANCHOR (TAG u) t ts)) = do
>     (displayTs :=>: _) <- distill es (ALLOWEDBY (evTm t) :>: ts)
>     return (DANCHOR u displayTs :=>: evTm x)


