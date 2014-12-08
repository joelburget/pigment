\section{Quotients}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Quotient where

%endif

|equivalenceRelation A R| is the proposition that |R| is an equivalence
relation over |A|.

> import -> RulesCode where
>   equivalenceRelation :: VAL -> VAL -> VAL
>   equivalenceRelation a r =
>     -- refl
>     AND (ALL a $ L $ "x" :. [.x. x =~ x ]) $
>     -- sym
>     AND (ALL a $ L $ "x" :. [.x.
>           ALL (a -$ []) $ L $ "y" :. [.y.
>            IMP (x =~ y) (y =~ x) ] ]
>         ) $
>     -- trans
>         (ALL a $ L $ "x" :. [.x.
>           ALL (a -$ []) $ L $ "y" :. [.y.
>            ALL (a -$ []) $ L $ "z" :. [.z.
>             IMP (x =~ y) (IMP (y =~ z) (x =~ z)) ] ] ]
>         )
>     where
>       x =~ y = r -$ [ NV x , NV y ]

> import -> Operators where
>   qElimOp :

> import -> OpCompile where
>   ("elimQuotient", [_, _, _, z, _, m, _]) -> App m [z]

> import -> OpCode where
>   qElimOp = Op
>     { opName  = "elimQuotient"
>     , opArity = 7
>     , opTyTel = "X" :<: SET                             :-: \_X ->
>                 "R" :<: ARR _X (ARR _X PROP)            :-: \_R ->
>                 "p" :<: PRF (equivalenceRelation _X _R) :-: \p ->
>                 "z" :<: QUOTIENT _X _R p                :-: \z ->
>                 "P" :<: ARR (QUOTIENT _X _R p) SET      :-: \_P ->
>                 "m" :<: (PI _X $ L $ "x" :. [.x. _P -$ [ CLASS (NV x) ] ])
>                                                         :-: \m ->
>                 "h" :<: PRF (ALL _X $ L $ "x" :. [.x.
>                               ALL (_X -$ []) $ L $ "y" :. [.y.
>                                IMP (_R -$ [ NV x , NV y ])
>                                 (EQBLUE (_P -$ [ CLASS (NV x) ]
>                                             :>: m -$ [ NV x ])
>                                         (_P -$ [ CLASS (NV y) ]
>                                             :>: m -$ [ NV y ])) ] ])
>                                                         :-: \_ ->
>                 Target $ _P $$ A z
>     , opRun = run
>     , opSimp = \_ _ -> empty
>     } where
>       run :: [VAL] -> Either NEU VAL
>       run [_, _, _, CLASS x, _, m, _] = Right (m $$ A x)
>       run [_, _, _, N n, _, _, _]     = Left n


> import -> OpRunEqGreen where
>   opRunEqGreen [QUOTIENT a r _, CLASS x, QUOTIENT b s _, CLASS y] =
>     Right $ ALL b $ L $ "x2" :. [.x2.
>               IMP (EQBLUE ((a -$ []) :>: (x -$ [])) ((b -$ []) :>: NV x2))
>                   (s -$ [NV x2 , y -$ [] ]) ]
>   opRunEqGreen [QUOTIENT a r _, N x, QUOTIENT b s _, _]   = Left x
>   opRunEqGreen [QUOTIENT a r _, _,   QUOTIENT b s _, N y] = Left y

> import -> Coerce where
>   coerce (Quotient (_X, _Y) _ _) q (CLASS x) = Right $
>     CLASS (coe @@ [_X, _Y, CON $ q $$ Fst, x])


> import -> KeywordConstructors where
>   KwQuotient  :: Keyword

> import -> KeywordTable where
>   key KwQuotient  = "Quotient"

> import -> DInTmParsersSpecial where
>   (AndSize, (|DQUOTIENT (%keyword KwQuotient%) (sizedDInTm ArgSize) (sizedDInTm ArgSize) (sizedDInTm ArgSize)|)) :


As a bit of syntactic sugar, we elaborate |con| as |COMPOSITE| and |[x]| as
|CLASS x|. \question{Why not just use |CON| rather than |COMPOSITE| everywhere?}

> import -> MakeElabRules where
>   makeElab' loc (MONAD d x :>: DCON t) =
>     makeElab' loc (MONAD d x :>: DCOMPOSITE t)
>   makeElab' loc (QUOTIENT a r p :>: DPAIR x DVOID) =
>     makeElab' loc (QUOTIENT a r p :>: DCLASS x)
