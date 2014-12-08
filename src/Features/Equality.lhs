\section{Equality}
\label{sec:Features.Equality}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Equality where

%endif



> import -> RulesCode where
>   cohAx = [("Axiom",0),("coh",0)] := (DECL :<: cohType) where
>     cohType = PRF $
>               ALL SET $ L $ "S" :. [._S.
>               ALL SET $ L $ "T" :. [._T.
>               ALL (PRF (EQBLUE (SET :>: NV _S) (SET :>: NV _T)))
>                  $ L $ "Q" :. [._Q.
>               ALL (NV _S) $ L $ "s" :. [.s.
>               EQBLUE (NV _S :>: NV s)
>                      (NV _T :>: N (coe :@ [NV _S, NV _T, NV _Q, NV s]))
>               ]]]]
>   refl = [("Axiom",0),("refl",0)] := (DECL :<: reflType) where
>     reflType = PRF $  ALL SET $ L $ "S" :. [._S.
>                       ALL (NV _S) $ L $ "s" :. [.s.
>                       EQBLUE (NV _S :>: NV s) (NV _S :>: NV s) ]]

>   substEq = [("Primitive", 0), ("substEq", 0)] := DEFN seDef :<: seTy where
>     seTy = PI SET $ L $ "X" :. [._X.
>                PI (NV _X) $ L $ "x" :. [.x.
>                PI (NV _X) $ L $ "y" :. [.y.
>                PI (PRF (EQBLUE (NV _X :>: NV x) (NV _X :>: NV y))) $ L $ "q" :. [.q.
>                PI (ARR (NV _X) SET) $ L $ "P" :. [._P.
>                ARR (N (V _P :$ A (NV x))) (N (V _P :$ A (NV y)))
>                ]]]]]
>     seDef = L $ "X" :. [._X.
>               L $ "x" :. [.x.
>               L $ "y" :. [.y.
>               L $ "q" :. [.q.
>               L $ "P" :. [._P.
>               L $ "px" :. [.px.
>               N (coe :@ [N (V _P :$ A (NV x)), N (V _P :$ A (NV y)),
>                   CON (N (P refl :$ A (ARR (NV _X) SET) :$ A (NV _P) :$ Out
>                             :$ A (NV x) :$ A (NV y) :$ A (NV q))),
>                   NV px])
>               ]]]]]]

>   symEq = [("Primitive", 0), ("symEq", 0)] := DEFN def :<: ty where
>     ty = PRF $ ALL SET $ L $ "X" :. [._X.
>                    ALL (NV _X) $ L $ "x" :. [.x.
>                    ALL (NV _X) $ L $ "y" :. [.y.
>                    IMP (EQBLUE (NV _X :>: NV x) (NV _X :>: NV y))
>                    (EQBLUE (NV _X :>: NV y) (NV _X :>: NV x))
>                ]]]
>     def = L $ "X" :. [._X.
>           L $ "x" :. [.x.
>           L $ "y" :. [.y.
>           L $ "q" :. [.q.
>           N (P refl :$ A (ARR (NV _X) SET)
>               :$ A (L $ "z" :. [.z.
>                   PRF (EQBLUE (NV _X :>: NV z) (NV _X :>: NV x))])
>               :$ Out
>               :$ A (NV x)
>               :$ A (NV y)
>               :$ A (NV q)
>               :$ Fst
>               :$ A (N (P refl :$ A (NV _X) :$ A (NV x))))
>           ]]]]

> import -> Primitives where
>   ("cohAx", cohAx) :
>   ("refl", refl) :
>   ("substEq", substEq) :
>   ("symEq", symEq) :


In the display syntax, a blue equality can be between arbitrary DExTms,
rather than ascriptions. To allow this, we add a suitable constructor |DEqBlue|
to DInTm, along with appropriate elaboration and distillation rules.

> import -> DInTmConstructors where
>   DEqBlue :: DExTm p x -> DExTm p x -> DInTm p x

> import -> DInTmPretty where
>   pretty (DEqBlue t u) = wrapDoc
>       (pretty t ArgSize <+> kword KwEqBlue <+> pretty u ArgSize)
>       ArgSize

> import -> DInTmReactive where
>   reactify (DEqBlue t u) = reactify t >> kword KwEqBlue >> reactify u

> import -> DInTmTraverse where
>   traverseDTIN f (DEqBlue t u) =
>     (| DEqBlue (traverseDTEX f t) (traverseDTEX f u) |)


> import -> KeywordConstructors where
>   KwEqBlue :: Keyword

> import -> KeywordTable where
>   key KwEqBlue = "=="

> import -> DInTmParsersMore where
>   (EqSize, \ t -> (| DEqBlue  (pFilter isEx (pure t)) (%keyword KwEqBlue%)
>                               (pFilter isEx (sizedDInTm (pred EqSize))) |)) :

> import -> ParserCode where
>   isEx :: DInTmRN -> Maybe DExTmRN
>   isEx (DN tm)  = Just tm
>   isEx _        = Nothing


> import -> MakeElabRules where
>   makeElab' loc (PROP :>: DEqBlue t u) = do
>       ttt <- subElabInfer loc t
>       utt <- subElabInfer loc u
>       let ttm :=>: tv :<: tty :=>: ttyv = extractNeutral ttt
>       let utm :=>: uv :<: uty :=>: utyv = extractNeutral utt
>       return $  EQBLUE (tty   :>: ttm)  (uty   :>: utm)
>           :=>:  EQBLUE (ttyv  :>: tv)   (utyv  :>: uv)

> import -> DistillRules where
>   distill es (PROP :>: tm@(EQBLUE (tty :>: t) (uty :>: u))) = do
>       t' <- toDExTm es (tty :>: t)
>       u' <- toDExTm es (uty :>: u)
>       return $ DEqBlue t' u' :=>: evTm tm

When distilling a proof of an equation, we first check to see if the equation
holds definitionally. If so, we avoid forcing the proof and return refl instead.

>   distill es (p@(PRF (EQBLUE (_S :>: s) (_T :>: t))) :>: q) = do
>       r <- askNSupply
>       if equal (SET :>: (_S, _T)) r && equal (_S :>: (s, t)) r
>           then return (DU :=>: N (P refl :$ A _S :$ A s))
>           else distillBase es (p :>: q)
