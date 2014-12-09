\section{IDesc}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.IDesc where

%endif

\subsection{Extending the display language}

We introduce a special DIMu for display purposes. While its definition
is the same than |IMu|, its "typing" is not: the label of an |IMu| is
presented as a lambda-bound anchor. When we are displaying a
particular |IMu|, we precisely know at which index we are considering
it. Therefore, a |DIMu| takes an anchor directly. The distillation
rule takes care of taking applying the lambda-bound anchor to the
index of |IMu| to make a fully applied anchor |DIMu|.

\subsection{Plugging Canonical terms in}



%if False

<  ("iinduction", [iI,d,i,v,bp,p]) -> App (Var "__iinduction") [d, p, i, v]
<  ("imapBox", [iI,d,x,bp,p,v]) -> App (Var "__imapBox") [d, p, v]

%endif





\subsection{Adding Primitive references in Cochon}


