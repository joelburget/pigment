\section{Enum}
\label{sec:Features.Enum}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Enum where

%endif




> import -> KeywordConstructors where
>   KwEnum  :: Keyword
>   KwPlus  :: Keyword

> import -> KeywordTable where
>   key KwEnum      = "Enum"
>   key KwPlus      = "+"

> import -> DInTmParsersSpecial where
>   (ArgSize, (|mkNum (|read digits|) (optional $ (keyword KwPlus) *> sizedDInTm ArgSize)|)) :
>   (AndSize, (|DENUMT (%keyword KwEnum%) (sizedDInTm ArgSize)|)) :

> import -> ParserCode where
>     mkNum :: Int -> Maybe DInTmRN -> DInTmRN
>     mkNum 0 Nothing = DZE
>     mkNum 0 (Just t) = t
>     mkNum n t = DSU (mkNum (n-1) t)

A function from an enumeration is equivalent to a list, so the elaborator can
turn lists into functions like this:

> import -> MakeElabRules where
>   makeElab' loc (PI (ENUMT e) t :>: m) | isTuply m = do
>       t' :=>: _ <- eQuote t
>       e' :=>: _ <- eQuote e
>       tm :=>: tmv <- subElab loc (branchesOp @@ [e, t] :>: m)
>       x <- eLambda (fortran t)
>       return $ N (switchOp :@ [e', NP x, t', tm])
>                      :=>: switchOp @@ [e, NP x, t, tmv]
>     where
>       isTuply :: DInTmRN -> Bool
>       isTuply DVOID        = True
>       isTuply (DPAIR _ _)  = True
>       isTuply _            = False


To elaborate a tag with an enumeration as its type, we search for the
tag in the enumeration to determine the appropriate index.

>   makeElab' loc (ENUMT t :>: DTAG a) = findTag a t 0
>     where
>       findTag :: String -> TY -> Int -> Elab (INTM :=>: VAL)
>       findTag a (CONSE (TAG b) t) n
>         | a == b        = return (toNum n :=>: toNum n)
>         | otherwise     = findTag a t (succ n)
>       findTag a _ n  = throwError . sErr $ "elaborate: tag `"
>                                             ++ a
>                                             ++ " not found in enumeration."
>
>       toNum :: Int -> Tm {In, p} x
>       toNum 0  = ZE
>       toNum n  = SU (toNum (n-1))

Conversely, we can distill an index to a tag as follows. Note that if the
index contains a stuck term, we simply give up and let the normal distillation
rules take over; the pretty-printer will then do the right thing.

> import -> DistillRules where
>   distill _ (ENUMT t :>: tm) | Just r <- findIndex (t :>: tm) = return r
>     where
>       findIndex :: (VAL :>: INTM) -> Maybe (DInTmRN :=>: VAL)
>       findIndex (CONSE (TAG s)  _ :>: ZE)    = Just (DTAG s :=>: evTm tm)
>       findIndex (CONSE _        a :>: SU b)  = findIndex (a :>: b)
>       findIndex _                            = Nothing

Since elaboration turns lists into functions from enumerated types, we can
do the reverse when distilling. This is slightly dubious.

>   distill es (PI (ENUMT e) t :>: L (x :. N (op :@ [e', NV 0, t', b])))
>     | op == switchOp = distill es (branchesOp @@ [e, t] :>: b)
