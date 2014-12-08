\section{Programming problems}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Problem where

%endif


\subsection{Plugging Canonical terms in}

> import -> CanReactive where

> import -> CanTraverse where
>   traverse _ Prob = (| Prob |)
>   traverse f (ProbLabel u s a) = (|ProbLabel (f u) (f s) (f a)|)
>   traverse f (PatPi u s p) = (|PatPi (f u) (f s) (f p)|)
>   traverse _ Sch = (| Sch |)
>   traverse f (SchTy t)      = (|SchTy (f t)|)
>   traverse f (SchExpPi s t) = (|SchExpPi (f s) (f t)|)
>   traverse f (SchImpPi s t) = (|SchImpPi (f s) (f t)|)

> import -> CanHalfZip where
>   halfZip Prob Prob = Just Prob
>   halfZip (ProbLabel u1 s1 a1) (ProbLabel u2 s2 a2) = Just $ ProbLabel (u1, u2) (s1, s2) (a1, a2)
>   halfZip (PatPi u1 s1 p1) (PatPi u2 s2 p2) = Just $ PatPi (u1, u2) (s1, s2) (p1, p2)
>   halfZip Sch Sch = Just Sch
>   halfZip (SchTy s1) (SchTy s2) = Just $ SchTy (s1, s2)
>   halfZip (SchExpPi s1 t1) (SchExpPi s2 t2) = Just $ SchExpPi (s1, s2) (t1, t2)
>   halfZip (SchImpPi s1 t1) (SchImpPi s2 t2) = Just $ SchImpPi (s1, s2) (t1, t2)

\subsection{Plugging Eliminators in}

> import -> ElimTyRules where

> import -> ElimComputation where

> import -> ElimCompile where

> import -> ElimTraverse where

> import -> ElimPretty where

> import -> ElimReactive where

\subsection{Plugging Operators in}

> import -> Operators where
>   argsOp :
>   schTypeOp :

> import -> OpCompile where

> import -> OpCode where
>   argsOp = Op
>     {  opName = "args"
>     ,  opArity = 1
>     ,  opTyTel = "s" :<: SCH :-: \ _ -> Target SET
>     ,  opRun = \ [s] -> argsOpRun s
>     ,  opSimp = \ _ _ -> empty
>     }

>   schTypeOp = Op
>     {  opName = "schType"
>     ,  opArity = 1
>     ,  opTyTel = "s" :<: SCH :-: \ _ -> Target SET
>     ,  opRun = \ [s] -> schTypeOpRun s
>     ,  opSimp = \ _ _ -> empty
>     }

>   argsOpRun :: VAL -> Either NEU VAL
>   argsOpRun (SCHTY _)       = Right UNIT
>   argsOpRun (SCHEXPPI s t)  =
>     Right $ SIGMA (schTypeOp @@ [s])
>              (L ("x" :. [.x. N $ argsOp :@ [t -$ [ NV x ]]]))
>   argsOpRun (SCHIMPPI s t)  =
>     Right $ SIGMA s
>              (L ("x" :. [.x. N $ argsOp :@ [t -$ [ NV x ]]]))
>   argsOpRun (N v)           = Left v

>   schTypeOpRun :: VAL -> Either NEU VAL
>   schTypeOpRun (SCHTY s)       = Right s
>   schTypeOpRun (SCHEXPPI s t)  =
>     Right $ PI (schTypeOp @@ [s])
>              (L ("x" :. [.x. N $ schTypeOp :@ [t -$ [ NV x ]]]))
>   schTypeOpRun (SCHIMPPI s t)  =
>     Right $ PI s
>              (L ("x" :. [.x. N $ schTypeOp :@ [t -$ [ NV x ]]]))
>   schTypeOpRun (N v)           = Left v


\subsection{Extending the type-checker}

> import -> Check where

\subsection{Extending the equality}

> import -> OpRunEqGreen where

> import -> Coerce where

\subsection{Extending the Display Language}

> import -> KeywordConstructors where
>   KwProb       :: Keyword
>   KwProbLabel  :: Keyword
>   KwPatPi      :: Keyword
>   KwSch        :: Keyword
>   KwSchTy      :: Keyword
>   KwExpPi      :: Keyword
>   KwImpPi      :: Keyword

> import -> KeywordTable where
>   key KwProb       = "Prob"
>   key KwProbLabel  = "ProbLabel"
>   key KwPatPi      = "PatPi"
>   key KwSch        = "Sch"
>   key KwSchTy      = "SchTy"
>   key KwExpPi      = "ExpPi"
>   key KwImpPi      = "ImpPi"

> import -> MakeElabRules where

> import -> DistillRules where

> import -> DInTmConstructors where

> import -> DInTmTraverse where

> import -> DInTmPretty where

> import -> DInTmReactive where

> import -> Pretty where

> import -> Reactive where

\subsection{Adding Primitive references in Cochon}

> import -> Primitives where
