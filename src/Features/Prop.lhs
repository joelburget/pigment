\section{Prop}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Prop where

%endif


Elim forms inherited from elsewhere

> import -> Pretty where
>   prettyAll :: Doc -> DInTmRN -> Size -> Doc
>   prettyAll bs (DALL (DPRF p) (DL (DK q))) = prettyAllMore bs
>     (pretty p (pred PiSize) <+> kword KwImp <+> pretty q PiSize)
>   prettyAll bs (DALL s (DL (x ::. t))) =
>     prettyAll (bs <> parens (text x <+> kword KwAsc <+> pretty s maxBound)) t
>   prettyAll bs (DALL s (DL (DK t))) = prettyAll bs (DALL s (DL ("_" ::. t)))
>   prettyAll bs (DALL s t) = prettyAllMore bs
>     (kword KwAll <+> pretty s minBound <+> pretty t minBound)
>   prettyAll bs tm = prettyAllMore bs (pretty tm PiSize)
>
>   prettyAllMore :: Doc -> Doc -> Size -> Doc
>   prettyAllMore bs d
>     | isEmpty bs  = wrapDoc d PiSize
>     | otherwise   = wrapDoc (bs <+> kword KwImp <+> d) PiSize

> import -> Reactive where
>   reactifyAll :: PureReact -> DInTmRN -> PureReact
>   reactifyAll bs (DALL (DPRF p) (DL (DK q))) = reactifyAllMore
>     bs
>     (reactify p >> reactKword KwImp >> reactify q)
>   reactifyAll bs (DALL s (DL (x ::. t))) = reactifyAll
>       (bs >> parens (fromString x >> reactKword KwAsc >> reactify s))
>       t
>   reactifyAll bs (DALL s (DL (DK t))) = reactifyAll bs
>       (DALL s (DL ("_" ::. t)))
>   reactifyAll bs (DALL s t) = reactifyAllMore bs
>     (reactKword KwAll >> reactify s >> reactify t)
>   reactifyAll bs tm = reactifyAllMore bs (reactify tm)
>
>   -- reactifyAllMore :: PureReact -> PureReact -> PureReact
>   -- reactifyAllMore bs d
>   --   | isEmpty bs  = wrapDoc d PiSize
>   --   | otherwise   = wrapDoc (bs <+> kword KwImp <+> d) PiSize
>
>   reactifyAllMore :: PureReact -> PureReact -> PureReact
>   reactifyAllMore bs d = bs >> reactKword KwImp >> d



> import -> Check where
>   check (PRF (ALL p q) :>: L sc)  = do
>     freshRef  ("" :<: p)
>               (\ref -> check (  PRF (q $$ A (pval ref)) :>:
>                                 underScope sc ref))
>     return $ L sc :=>: (evTm $ L sc)

> import -> OpRunEqGreen where
>   opRunEqGreen [PROP,t1,PROP,t2] = Right $ AND (IMP t1 t2) (IMP t2 t1)
>   opRunEqGreen [PRF _,_,PRF _,_] = Right TRIVIAL

> import -> Coerce where
>   coerce Prop              q pP  = Right pP
>   coerce (Prf (pP1, pP2))  q p   = Right $ q $$ Fst $$ A p


> import -> KeywordConstructors where
>    KwProp     :: Keyword
>    KwAbsurd   :: Keyword
>    KwTrivial  :: Keyword
>    KwPrf      :: Keyword
>    KwAnd      :: Keyword
>    KwArr      :: Keyword
>    KwImp      :: Keyword
>    KwAll      :: Keyword
>    KwInh      :: Keyword
>    KwWit      :: Keyword

> import -> KeywordTable where
>   key KwProp      = "Prop"
>   key KwAbsurd    = "FF"
>   key KwTrivial   = "TT"
>   key KwPrf       = ":-"
>   key KwAnd       = "&&"
>   key KwArr       = "->"
>   key KwImp       = "=>"
>   key KwAll       = "All"
>   key KwInh       = "Inh"
>   key KwWit       = "wit"

> import -> DInTmParsersSpecial where
>   (ArgSize, (|DPROP     (%keyword KwProp%)|)) :
>   (ArgSize, (|DABSURD   (%keyword KwAbsurd%)|)) :
>   (ArgSize, (|DTRIVIAL  (%keyword KwTrivial%)|)) :
>   (AndSize, (|DPRF      (%keyword KwPrf%) (sizedDInTm AndSize)|)) :
>   (AndSize, (|DINH      (%keyword KwInh%) (sizedDInTm ArgSize)|)) :
>   (AndSize, (|DWIT      (%keyword KwWit%) (sizedDInTm ArgSize)|)) :
>   (AndSize, (|DALL      (%keyword KwAll%) (sizedDInTm ArgSize) (sizedDInTm ArgSize)|)) :

> import -> DInTmParsersMore where
>   (AndSize, \ s -> (| (DAND s) (%keyword KwAnd%) (sizedDInTm AndSize)  |)) :
>   (ArrSize, \ s -> (| (DIMP s) (%keyword KwImp%) (sizedDInTm PiSize)   |)) :



> import -> DistillRules where
>   distill es (PRF TRIVIAL :>: _) = return (DU :=>: VOID)
