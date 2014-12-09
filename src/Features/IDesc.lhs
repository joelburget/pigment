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



> import -> DistillRules where

>     distill es (IMU l _I s i :>: CON (PAIR t x))
>       | Just (e, f) <- sumilike _I (s $$ A i) = do
>         m   :=>: tv  <- distill es (ENUMT e :>: t)
>         as  :=>: xv  <-
>           distill es (idescOp @@ [  _I,f tv
>                                  ,  L $ "i" :. [.i.
>                                       IMU (fmap (-$ []) l)
>                                           (_I -$ []) (s -$ []) (NV i)]
>                                  ] :>: x)
>         case m of
>             DTAG s   -> return $ DTag s (unfold as)  :=>: CON (PAIR tv xv)
>             _        -> return $ DCON (DPAIR m as)   :=>: CON (PAIR tv xv)
>       where
>         unfold :: DInTmRN -> [DInTmRN]
>         unfold DVOID        = []
>         unfold DU        = []
>         unfold (DPAIR s t)  = s : unfold t
>         unfold t            = [t]


>     distill es (SET :>: tm@(C (IMu ltm@(Just l :?=: (Id _I :& Id s)) i))) = do
>       let lab = evTm ((l :? ARR _I ANCHORS) :$ A i)
>       labTm                <- bquoteHere lab
>       (labDisplay :=>: _)  <- distill es (ANCHORS :>: labTm)
>       _It :=>: _Iv         <- distill es (SET :>: _I)
>       st :=>: sv           <- distill es (ARR _Iv (idesc $$ A _Iv) :>: s)
>       it :=>: iv           <- distill es (_Iv :>: i)
>       return $ (DIMU (Just labDisplay) _It st it :=>: evTm tm)


\subsection{Adding Primitive references in Cochon}


