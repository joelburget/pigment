\section{A universe of descriptions: |Desc|}
\label{sec:Features.Desc}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Desc where

%endif




The |mkLazyDescDef| function lazily eliminates a desc value (i.e. |d| such that
|desc :>: CON d|. If the tag is canonical, it calls the corresponding case in
the dispatch table with the relevant arguments; otherwise, it cannot compute,
so it returns a term on the |Left|. Note that finite sums are handled using the
case for sigma.

<   mkLazyDescDef :: VAL -> DescDispatchTable -> Either NEU VAL
<   mkLazyDescDef arg (idCase, constCase, prodCase, sigmaCase, piCase) =
<       let args = arg $$ Snd in
<         case arg $$ Fst of
<           IDN     -> Right $ idCase
<           CONSTN  -> Right $ constCase  (args $$ Fst)
<           SUMN    -> Right $ sigmaCase  (ENUMT (args $$ Fst)) (args $$ Snd $$ Fst)
<           PRODN   -> Right $ prodCase   (args $$ Fst) (args $$ Snd $$ Fst)
<           SIGMAN  -> Right $ sigmaCase  (args $$ Fst) (args $$ Snd $$ Fst)

<           PIN     -> Right $ piCase     (args $$ Fst) (args $$ Snd $$ Fst)
<           N t     -> Left t
<           _       -> error "mkLazyDescDef: invalid constructor!"
