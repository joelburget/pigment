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

> import -> DInTmConstructors where
>   DIMu :: Labelled (Id :*: Id) (DInTm p x) -> DInTm p x  -> DInTm p x

> import -> DInTmTraverse where
>   traverseDTIN f (DIMu s i) = (|DIMu (traverse (traverseDTIN f) s) (traverseDTIN f i)|)

> import -> DInTmPretty where
>   pretty (DIMu (Just s   :?=: _) _)  = pretty s
>   pretty (DIMu (Nothing  :?=: (Id ii :& Id d)) i)  = wrapDoc
>       (kword KwIMu <+> pretty ii ArgSize <+> pretty d ArgSize <+> pretty i ArgSize)
>       AppSize

> import -> DInTmReactive where
>   reactify (DIMu (Just s   :?=: _) _)  = reactify s
>   reactify (DIMu (Nothing  :?=: (Id ii :& Id d)) i)  = do
>       reactKword KwIMu
>       reactify ii
>       reactify d
>       reactify i

\subsection{Plugging Canonical terms in}


> import -> Coerce where
>   -- coerce :: (Can (VAL,VAL)) -> VAL -> VAL -> Either NEU VAL
>   coerce (IMu (Just (l0,l1) :?=:
>               (Id (iI0,iI1) :& Id (d0,d1))) (i0,i1)) q (CON x) =
>     let ql  = CON $ q $$ Fst
>         qiI = CON $ q $$ Snd $$ Fst
>         qi  = CON $ q $$ Snd $$ Snd $$ Snd
>         qd = CON $ q $$ Snd $$ Snd $$ Fst
>         typ =
>           PI SET $ L $ "iI" :. [.iI.
>            ARR (ARR (NV iI) (idesc -$ [ NV iI ])) $
>             ARR (NV iI) $
>              ARR (ARR (NV iI) ANCHORS) SET ]
>         vap =
>           L $ "iI" :. [.iI.
>            L $ "d" :. [.d.
>             L $ "i" :. [.i.
>              L $ "l" :. [.l. N $
>               idescOp :@ [ NV iI , N (V d :$ A (NV i))
>                          , L $ "j" :. [.j.
>                             IMU (|(NV l)|) (NV iI) (NV d) (NV j)]
>                          ] ] ] ] ]
>     in Right . CON $
>       coe @@ [ idescOp @@ [  iI0, d0 $$ A i0
>                           ,  L $ "i" :. [.i.
>                               IMU (|(l0 -$ [])|) (iI0 -$ []) (d0 -$ []) (NV i)
>                              ]
>                           ]
>              , idescOp @@ [  iI1, d1 $$ A i1
>                           ,  L $ "i" :. [.i.
>                               IMU (|(l1 -$ [])|) (iI1 -$ []) (d1 -$ []) (NV i)
>                              ]
>                           ]
>              , CON $ pval refl $$ A typ $$ A vap $$ Out
>                                $$ A iI0 $$ A iI1 $$ A qiI
>                                $$ A d0 $$ A d1 $$ A qd
>                                $$ A i0 $$ A i1 $$ A qi
>                                $$ A l0 $$ A l1 $$ A ql
>              , x ]
>   coerce (IMu (Nothing :?=: (Id (iI0,iI1) :& Id (d0,d1))) (i0,i1)) q (CON x) =
>     let qiI = CON $ q $$ Fst
>         qi  = CON $ q $$ Snd $$ Snd
>         qd = CON $ q $$ Snd $$ Fst
>         typ =
>           PI SET $ L $ "iI" :. [.iI.
>            ARR (ARR (NV iI) (idesc -$ [ NV iI ])) $
>             ARR (NV iI) SET ]
>         vap =
>           L $ "iI" :. [.iI.
>            L $ "d" :. [.d.
>             L $ "i" :. [.i. N $
>               idescOp :@ [ NV iI , N (V d :$ A (NV i))
>                          , L $ "j" :. [.j.
>                             IMU Nothing (NV iI) (NV d) (NV j)]
>                          ] ] ] ]
>     in Right . CON $
>       coe @@ [ idescOp @@ [ iI0 , d0 $$ A i0
>                           , L $ "i" :. [.i.
>                               IMU Nothing (iI0 -$ []) (d0 -$ []) (NV i) ] ]
>              , idescOp @@ [ iI1 , d1 $$ A i1
>                           , L $ "i" :. [.i.
>                               IMU Nothing (iI1 -$ []) (d1 -$ []) (NV i) ] ]
>              , CON $ pval refl $$ A typ $$ A vap $$ Out
>                                $$ A iI0 $$ A iI1 $$ A qiI
>                                $$ A d0 $$ A d1 $$ A qd
>                                $$ A i0 $$ A i1 $$ A qi
>              , x ]


%if False

<  ("iinduction", [iI,d,i,v,bp,p]) -> App (Var "__iinduction") [d, p, i, v]
<  ("imapBox", [iI,d,x,bp,p,v]) -> App (Var "__imapBox") [d, p, v]

%endif


> import -> KeywordConstructors where
>   KwIMu :: Keyword

> import -> KeywordTable where
>   key KwIMu      = "IMu"

> import -> DInTmParsersSpecial where
>   (AndSize, (|(DIMU Nothing) (%keyword KwIMu%) (sizedDInTm ArgSize) (sizedDInTm ArgSize) (sizedDInTm ArgSize)|)) :

> import -> MakeElabRules where

>   makeElab' loc (SET :>: DIMU Nothing iI d i) = do
>       iI  :=>: iIv  <- subElab loc (SET :>: iI)
>       d   :=>: dv   <- subElab loc (ARR iIv (idesc $$ A iIv) :>: d)
>       i   :=>: iv   <- subElab loc (iIv :>: i)
>       return $ IMU Nothing iI d i :=>: IMU Nothing iIv dv iv

>   makeElab' loc (ty@(IMU _ _ _ _) :>: DTag s xs) =
>       makeElab' loc (ty :>: DCON (DPAIR (DTAG s) (foldr DPAIR DU xs)))

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


