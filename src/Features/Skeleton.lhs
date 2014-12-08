\section{Skeleton feature}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Skeleton where

%endif


\subsection{Plugging in canonical forms}

\subsection{Plugging in eliminators}

> import -> ElimTyRules where

> import -> ElimComputation where

> import -> ElimCompile where

> import -> ElimTraverse where

> import -> ElimPretty where

> import -> ElimReactive where

\subsection{Plugging in operators}

> import -> Operators where

> import -> OpCompile where

> import -> OpCode where

\subsection{Plugging in axioms and primitives}

> import -> RulesCode where

> import -> Primitives where

\subsection{Extending the type-checker}

> import -> Check where

\subsection{Extending the equality}

> import -> OpRunEqGreen where

> import -> Coerce where

\subsection{Extending the display language}

> import -> DInTmConstructors where

> import -> DInTmTraverse where

> import -> DInTmPretty where

> import -> DInTmReactive where

> import -> Pretty where

> import -> Reactive where

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
