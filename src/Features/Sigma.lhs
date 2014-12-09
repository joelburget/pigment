\section{Sigma}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Sigma where

%endif


> import -> Reactive where
>   reactifyPair :: DInTmRN -> PureReact
>   reactifyPair p = "[" >> reactifyPairMore "" p >> "]"

>   reactifyPairMore :: PureReact -> DInTmRN -> PureReact
>   reactifyPairMore d DVOID        = d
>   reactifyPairMore d (DPAIR a b)  = reactifyPairMore
>       (d >> reactify a)
>       b
>   reactifyPairMore d t            = d >> reactKword KwComma >> reactify t

>   reactifySigma :: PureReact -> DInTmRN -> PureReact
>   reactifySigma d DUNIT                      = reactifySigmaDone d ""
>   reactifySigma d (DSIGMA s (DL (x ::. t)))  = reactifySigma
>       (d >> fromString x >> reactKword KwAsc >> reactify s >> reactKword KwSemi)
>       t
>   reactifySigma d (DSIGMA s (DL (DK t)))     = reactifySigma
>       (d >> reactify s >> reactKword KwSemi) t
>   reactifySigma d (DSIGMA s t) = reactifySigmaDone d
>       (reactKword KwSig >> reactify s >> reactify t)
>   reactifySigma d t = reactifySigmaDone d (reactify t)

>   reactifySigmaDone :: PureReact -> PureReact -> PureReact
>   reactifySigmaDone s t = reactKword KwSig >> "(" >> s >> t >> ")"

>   -- reactifySigmaDone :: PureReact -> PureReact -> PureReact
>   -- reactifySigmaDone s t
>   --   | isEmpty s  = wrapDoc t AppSize
>   --   | otherwise  = wrapDoc (kword KwSig <+> parens (s <+> t)) AppSize


> import -> KeywordConstructors where
>   KwFst  :: Keyword
>   KwSnd  :: Keyword
>   KwSig  :: Keyword

> import -> KeywordTable where
>   key KwFst       = "!"
>   key KwSnd       = "-"
>   key KwSig       = "Sig"

> import -> ElimParsers where
>   (AppSize, (| Fst (%keyword KwFst%) |)) :
>   (AppSize, (| Snd (%keyword KwSnd%) |)) :

> import -> DInTmParsersSpecial where
>   (ArgSize, (|id (bracket Square tuple)|)) :
>   (ArgSize, (|id (%keyword KwSig%) (bracket Round sigma)|)) :
>   (ArgSize, (|DSIGMA (%keyword KwSig%) (sizedDInTm ArgSize) (sizedDInTm ArgSize)|)) :

> import -> ParserCode where
>     tuple :: Parsley Token DInTmRN
>     tuple =
>         (|DPAIR (sizedDInTm ArgSize) (| id (%keyword KwComma%) pDInTm
>                                       | id tuple |)
>          |DVOID (% pEndOfStream %)
>          |)

>     sigma :: Parsley Token DInTmRN
>     sigma = (|mkSigma (optional (ident <* keyword KwAsc)) pDInTm sigmaMore
>              |DUNIT (% pEndOfStream %)
>              |)

>     sigmaMore :: Parsley Token DInTmRN
>     sigmaMore = (|id (% keyword KwSemi %) (sigma <|> pDInTm)
>                  |(\p s -> mkSigma Nothing (DPRF p) s) (% keyword KwPrf %) pDInTm sigmaMore
>                  |(\x -> DPRF x) (% keyword KwPrf %) pDInTm
>                  |)

>     mkSigma :: Maybe String -> DInTmRN -> DInTmRN -> DInTmRN
>     mkSigma Nothing s t = DSIGMA s (DL (DK t))
>     mkSigma (Just x) s t = DSIGMA s (DL (x ::. t))



In order to make programs as cryptic as possible, you can use |con| in the
display language to generate a constant function from unit or curry a function
from a pair.

> import -> MakeElabRules where
>   makeElab' loc (PI UNIT t :>: DCON f) = do
>     tm :=>: tmv <- subElab loc (t $$ A VOID :>: f)
>     return $ LK tm :=>: LK tmv

>   makeElab' loc (PI (SIGMA d r) t :>: DCON f) = do
>     let mt =  PI d . L $ (fortran r) :. [.a.
>               PI (r -$ [NV a]) . L $ (fortran t) :. [.b.
>               t -$ [PAIR (NV a) (NV b)] ] ]
>     mt'  :=>: _    <- eQuote mt
>     tm   :=>: tmv  <- subElab loc (mt :>: f)
>     x <- eLambda (fortran t)
>     return $ N ((tm :? mt') :$ A (N (P x :$ Fst)) :$ A (N (P x :$ Snd)))
>                     :=>: tmv $$ A (NP x $$ Fst) $$ A (NP x $$ Snd)


> import -> DistillRules where
>   distill es (UNIT :>: _) = return $ DVOID :=>: VOID
