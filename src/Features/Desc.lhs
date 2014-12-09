\section{A universe of descriptions: |Desc|}
\label{sec:Features.Desc}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Desc where

%endif




The |mkLazyDescDef| function lazily eliminates a desc value (i.e. |d| such that
|desc :>: CON d|. If the tag is canonical, it calls the corresponding case in
the dispatch table with the relevant arguments; otherwise, it cannot compute,
so it returns a term on the |Left|. Note that finite sums are handled using the
case for sigma.

>   mkLazyDescDef :: VAL -> DescDispatchTable -> Either NEU VAL
>   mkLazyDescDef arg (idCase, constCase, prodCase, sigmaCase, piCase) =
>       let args = arg $$ Snd in
>         case arg $$ Fst of
>           IDN     -> Right $ idCase
>           CONSTN  -> Right $ constCase  (args $$ Fst)
>           SUMN    -> Right $ sigmaCase  (ENUMT (args $$ Fst)) (args $$ Snd $$ Fst)
>           PRODN   -> Right $ prodCase   (args $$ Fst) (args $$ Snd $$ Fst)
>           SIGMAN  -> Right $ sigmaCase  (args $$ Fst) (args $$ Snd $$ Fst)

>           PIN     -> Right $ piCase     (args $$ Fst) (args $$ Snd $$ Fst)
>           N t     -> Left t
>           _       -> error "mkLazyDescDef: invalid constructor!"

>   descOp :: Op
>   descOp = Op
>     { opName = "desc"
>     , opArity = 2
>     , opTyTel = dOpTy
>     , opRun = {- dOpRun -} runOpTree $ oData
>         [ {-ID-} oTup $ OLam $ \_X -> ORet _X
>         , {-CONST-} oTup $ \_A -> OLam $ \_X -> ORet _A
>         , {-SUM-} oTup $ \_E _D -> OLam $ \_X -> ORet $
>                     SIGMA (ENUMT _E) $ L $ "c" :. [.c. N $
>                        descOp :@ [_D -$ [NV c], _X -$ []]]
>         , {-PROD-} oTup $ \u _D _D' -> OLam $ \_X -> ORet $
>                     SIGMA (descOp @@ [_D, _X])
>                           (L $ (unTag u) :. (N $ descOp :@ [_D' -$ [], _X -$ []]))
>         , {-SIGMA-} oTup $ \_S _D -> OLam $ \_X -> ORet $
>                     SIGMA _S $ L $ (fortran _D) :. [.s. N $
>                       descOp :@ [_D -$ [NV s], _X -$ []]]
>         , {-PI-} oTup $ \_S _D -> OLam $ \_X -> ORet $
>                     PI _S $ L $ (fortran _D) :. [.s. N $
>                       descOp :@ [_D -$ [NV s], _X -$ []]]
>         ]
>     , opSimp = \_ _ -> empty
>     } where
>       dOpTy =
>         "D" :<: desc :-: \dD ->
>         "X" :<: SET :-: \xX ->
>         Target SET

>   unTag :: VAL -> String
>   unTag (TAG u) = u
>   unTag _ = "x"
>   boxOp :: Op
>   boxOp = Op
>     { opName = "box"
>     , opArity = 4
>     , opTyTel = boxOpTy
>     , opRun = {-boxOpRun-} runOpTree $ oData
>         [ {-ID-} oTup $             oLams $ \ () _P x -> ORet (_P $$ A x)
>         , {-CONST-} oTup $ \ () ->  oLams $ \ () () () -> ORet UNIT
>         , {-SUM-} oTup $ \ () _D -> oLams $ \_X _P -> OPr $ oLams $ \c d ->
>              ORet $ boxOp @@ [_D $$ A c, _X, _P, d]
>         , {-PROD-} oTup $ \u _D _D' -> oLams $ \_X _P -> OPr $ oLams $ \d d' ->
>              ORet $ SIGMA (boxOp @@ [_D, _X, _P, d]) (L $ (unTag u ++ "h") :.
>                        (N (boxOp :@ [_D' -$ [], _X -$ [], _P -$ [], d' -$ []])))
>         , {-SIGMA-} oTup $ \ () _D -> oLams $ \_X _P -> OPr $ oLams $ \s d ->
>              ORet $ boxOp @@ [_D $$ A s, _X, _P, d]
>         , {-PI-} oTup $ \_S _D -> oLams $ \_X _P f ->
>              ORet $ PI _S $ L $ (fortran _D) :. [.s. N $
>                 boxOp :@ [_D -$ [NV s], _X -$ [] , _P -$ [] , f -$ [NV s]]]
>         ]
>     , opSimp = \_ _ -> empty
>     } where
>       boxOpTy =
>         "D" :<: desc :-: \dD ->
>         "X" :<: SET :-: \xX ->
>         "P" :<: ARR xX SET :-: \pP ->
>         "v" :<: (descOp @@ [dD,xX]) :-: \v ->
>         Target SET

>   mapBoxOp :: Op
>   mapBoxOp = Op
>     { opName = "mapBox"
>     , opArity = 5
>     , opTyTel = mapBoxOpTy
>     , opRun = {-mapBoxOpRun-} runOpTree $ oData
>       [ {-ID-} oTup $             oLams $ \ () () p x -> ORet (p $$ A x)
>       , {-CONST-} oTup $ \ () ->  oLams $ \ () () () () -> ORet VOID
>       , {-SUM-} oTup $ \ () _D -> oLams $ \_X _P p -> OPr $ oLams $ \c d ->
>            ORet $ mapBoxOp @@ [_D $$ A c, _X, _P, p, d]
>       , {-PROD-} oTup $ \() _D _D' -> oLams $ \_X _P p -> OPr $ oLams $ \d d' ->
>            ORet $ PAIR (mapBoxOp @@ [_D, _X, _P, p, d])
>                        (mapBoxOp @@ [_D', _X, _P, p, d'])
>       , {-SIGMA-} oTup $ \ () _D -> oLams $ \_X _P p -> OPr $ oLams $ \s d ->
>            ORet $ mapBoxOp @@ [_D $$ A s, _X, _P, p, d]
>       , {-PI-} oTup $ \() _D -> oLams $ \_X _P p f ->
>            ORet $ L $ (fortran _D) :. [.s. N $
>              mapBoxOp :@ [_D -$ [NV s], _X -$ [] , _P -$ [] , p -$ [],
>                            f -$ [NV s]]]
>       ]
>     , opSimp = \_ _ -> empty
>     } where
>       mapBoxOpTy =
>         "D" :<: desc :-: \ dD ->
>         "X" :<: SET :-: \ xX ->
>         "P" :<: ARR xX SET :-: \ pP ->
>         "p" :<: (PI xX $ L $ "x" :. [.x. pP -$ [ NV x ] ]) :-: \ _ ->
>         "v" :<: (descOp @@ [dD,xX]) :-: \v ->
>          Target (boxOp @@ [dD,xX,pP,v])

>   mapOp = Op
>     { opName  = "map"
>     , opArity = 5
>     , opTyTel    = mapOpTy
>     , opRun   = {-mapOpRun-} runOpTree $ oData
>       [ {-ID-} oTup $ oLams $ \ () () f v -> ORet $ f $$ A v
>       , {-CONST-} oTup $ \ () -> oLams $ \ () () () a -> ORet a
>       , {-SUM-} oTup $ \ () _D -> oLams $ \_X _Y f -> OPr $ oLams $ \c d ->
>           ORet $ PAIR c (mapOp @@ [_D $$ A c, _X, _Y, f, d])
>       , {-PROD-} oTup $ \() _D _D' -> oLams $ \_X _Y f -> OPr $ oLams $ \d d' ->
>           ORet $ PAIR (mapOp @@ [_D, _X, _Y, f, d])
>                       (mapOp @@ [_D', _X, _Y, f, d'])
>       , {-SIGMA-} oTup $ \ () _D -> oLams $ \_X _Y f -> OPr $ oLams $ \s d ->
>            ORet $ PAIR s (mapOp @@ [_D $$ A s, _X, _Y, f, d])
>       , {-PI-} oTup $ \() _D -> oLams $ \_X _Y f g ->
>            ORet $ L $ (fortran _D) :. [.s. N $
>              mapOp :@ [_D -$ [NV s], _X -$ [] , _Y -$ [] , f -$ [],
>                            g -$ [NV s]]]
>       ]
>     , opSimp  = mapOpSimp
>     } where
>         mapOpTy =
>           "dD" :<: desc :-: \dD ->
>           "xX" :<: SET :-: \xX ->
>           "yY" :<: SET :-: \yY ->
>           "f" :<: ARR xX yY :-: \f ->
>           "v" :<: (descOp @@ [dD, xX]) :-: \v ->
>           Target (descOp @@ [dD, yY])
>         mapOpSimp :: Alternative m => [VAL] -> NameSupply -> m NEU
>         mapOpSimp [dD, xX, yY, f, N v] r
>           | equal (SET :>: (xX, yY)) r &&
>             equal (ARR xX yY :>: (f, identity)) r = pure v
>           where
>             identity = L $ "x" :. [.x. NV x]
>         mapOpSimp [dD, _, zZ, f, N (mOp :@ [_, xX, _, g, N v])] r
>           | mOp == mapOp = mapOpSimp args r <|> pure (mapOp :@ args)
>           where
>             comp f g = L $ "x" :. [.x. f -$ [g -$ [NV x]]]
>             args = [dD, xX, zZ, comp f g, N v]
>         mapOpSimp _ _ = empty

>   inductionOpMethodType = L $ "d" :. [.d.
>                      L $ "P" :. [._P.
>                      PI (N $ descOp :@ [NV d, MU Nothing (NV d)])
>                         (L $ "x" :. [.x.
>                          ARR (N $ boxOp :@ [NV d, MU Nothing (NV d), NV _P, NV x])
>                              (N (V _P :$ A (CON (NV x)))) ]) ] ]

>   inductionOpLabMethodType = L $ "l" :. [.l.
>                      L $ "d" :. [.d.
>                      L $ "P" :. [._P.
>                      PI (N $ descOp :@ [NV d, MU (|(NV l)|) (NV d)])
>                         (L $ "x" :. [.x.
>                          ARR (N $ boxOp :@ [NV d, MU (|(NV l)|) (NV d), NV _P, NV x])
>                              (N (V _P :$ A (CON (NV x)))) ]) ] ] ]


>   inductionOp :: Op
>   inductionOp = Op
>     { opName = "induction"
>     , opArity = 4
>     , opTyTel = inductionOpTy
>     , opRun = {-inductionOpRun-} runOpTree $
>         OLam $ \ _D -> OCon $ oLams $ \ v _P p -> ORet $
>           p $$ A v $$ A (mapBoxOp @@ [_D, MU Nothing _D, _P,
>             L $ "x" :. [.x. N $
>              inductionOp :@ [_D -$ [], NV x, _P -$ [], p -$ []]], v])
>     , opSimp = \_ _ -> empty
>     } where
>       inductionOpTy =
>         "D" :<: desc :-: \dD ->
>         "v" :<: MU Nothing dD :-: \v ->
>         "P" :<: (ARR (MU Nothing dD) SET) :-: \pP ->
>         "p" :<: (inductionOpMethodType $$ A dD $$ A pP) :-: \p ->
>         Target (pP $$ A v)

>   branchesDOp = Op
>     { opName   = "branchesD"
>     , opArity  = 1
>     , opTyTel  = bOpTy
>     , opRun    = runOpTree $
>         oData  [ oTup $ ORet UNIT
>                , oTup $ \ () _E -> ORet $
>                  TIMES desc
>                     (branchesDOp @@ [_E])
>                ]
>     , opSimp   = \_ _ -> empty
>     } where
>         bOpTy = "e" :<: enumU :-: \e ->
>                 Target SET



>   switchDOp = Op
>     { opName = "switchD"
>     , opArity = 3
>     , opTyTel = sOpTy
>     , opRun =  runOpTree $
>         OLam $ \_ -> OLam $ \bs ->
>         OCase (map (\x -> proj x bs) [0..])
>     , opSimp = \_ _ -> empty
>     } where
>         sOpTy =
>           "e" :<: enumU :-: \e ->
>           "b" :<: (branchesDOp @@ [e]) :-: \b ->
>           "x" :<: ENUMT e :-: \x ->
>           Target desc
>         proj 0 bs = ORet (bs $$ Fst)
>         proj i bs = (proj (i - 1) (bs $$ Snd))




\subsection{Extending the Display Language}





> import -> DistillRules where

The following cases turn vaguely list-like data into actual lists.
We don't want this in general, but it is useful in special cases (when the data
type is really supposed to be a list, as in |EnumD|).
\question{When else should we use this representation?}

>     distill _ (MU (Just (ANCHOR (TAG r) _ _)) _ :>: CON (PAIR ZE VOID)) | r == "EnumU" =
>         return (DVOID :=>: CON (PAIR ZE VOID))

>     distill es (C ty@(Mu (Just (ANCHOR (TAG r) _ _) :?=: _)) :>:
>       C c@(Con (PAIR (SU ZE) (PAIR _ (PAIR _ VOID)))))
>       | r == "EnumU" = do
>         Con (DPAIR _ (DPAIR s (DPAIR t _)) :=>: v) <- canTy  (distill es)
>                                                              (ty :>: c)
>         return ((DPAIR s t) :=>: CON v)


If we have a canonical value in |MU s|, where |s| starts with a finite sum,
then we can (probably) turn it into a tag applied to some arguments.

>     distill es (ty@(MU l s) :>: CON (PAIR t x)) | Just (e, f) <- sumlike s = do
>         m   :=>: tv  <- distill es (ENUMT e :>: t)
>         as  :=>: xv  <- distill es (descOp @@ [f tv, ty] :>: x)
>         case m of
>             DTAG s   -> return $ DTag s (unfold as)  :=>: CON (PAIR tv xv)
>             _        -> return $ DCON (DPAIR m as)   :=>: CON (PAIR tv xv)
>       where
>         unfold :: DInTmRN -> [DInTmRN]
>         unfold DU           = [] -- since DVOID gets turned into this first
>         unfold DVOID        = []
>         unfold (DPAIR s t)  = s : unfold t
>         unfold t            = [t]

The |sumlike| function determines whether a value representing a description
is a sum or a sigma from an enumerate. If so, it returns |Just| the enumeration
and a function from the enumeration to descriptions.
\question{Where should this live?}

>   sumlike :: VAL -> Maybe (VAL, VAL -> VAL)
>   sumlike (SUMD e b)            = Just (e, (b $$) . A)
>   sumlike (SIGMAD (ENUMT e) f)  = Just (e, (f $$) . A)
>   sumlike _                     = Nothing
