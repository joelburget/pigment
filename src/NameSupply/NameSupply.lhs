\section{NameSupply}

%if False

\begin{code}
{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE TypeOperators #-}
module NameSupply.NameSupply where
import Kit.BwdFwd
import Kit.MissingLibrary
\end{code}
%endif

The |NameSupply| is the name generator used throughout Epigram. It is
inspired by the \emph{hierarchical names}~\cite{mcbride:free_variable}
used in Epigram the First. The aim of this structure is to
conveniently, provide unique free variable names.

A |NameSupply| is composed by a backward list of |(String, Int)| and an
|Int|. This corresponds to a hierarchical namespace and a free name in
that namespace. The structure of the namespace stack is justified as
follows. The |String| component provides name advice, which may not be
unique, while the |Int| uniquely identifies the namespace.

\begin{code}
type NameSupply = (Bwd (String, Int), Int)
\end{code}
Therefore, creating a fresh name in a given namespace simply consists
of incrementing the name counter:

\begin{code}
freshName :: NameSupply -> NameSupply
freshName (sis, i) = (sis, i + 1)
\end{code}
Whereas creating a fresh namespace involves stacking up a new name
|s|, uniquely identified by |i|, and initializing the per-namespace
counter to |0|:

\begin{code}
freshNSpace :: NameSupply -> String -> NameSupply
freshNSpace (sis, i) s = (sis :< (s,i), 0)
\end{code}
Intuitively, the function |name| computes a fresh name out of a given
name generator, decorating it with the human-readable label
|s|. Technically, |Name| is defined as
a list of |(String, Int)|. Hence, on that structure, the effect of
|trail| is to flatten the backward namespace into a (unique) |Name|.

\begin{code}
type Name = [(String, Int)]
mkName :: NameSupply -> String -> Name
mkName (sis, i) s = trail $ sis :< (s, i)
\end{code}
