\section{Operators and primitives}
\label{sec:Evidences.Operators}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts, PatternGuards #-}

> module Evidences.Operators where

> import Control.Applicative

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import Evidences.Tm
> import {-# SOURCE #-} Evidences.Eval
> import Evidences.OperatorDSL
> import {-# SOURCE #-} Evidences.DefinitionalEquality
> import {-# SOURCE #-} Evidences.PropositionalEquality
> import {-# SOURCE #-} Evidences.BetaQuotation

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import Features.Features ()

%endif


In this section, we weave some She aspects. In particular, we bring
inside @Rules.lhs@ the |operators| defined by feature files,
along with any auxiliary code.

> operators :: [Op]
> operators = [
>   descOp,
>   boxOp,
>   mapBoxOp,
>   mapOp,
>   inductionOp,
>   branchesDOp,
>   switchDOp,
>   branchesOp,
>   switchOp,
>   enumInductionOp,
>   eqGreen,
>   coe,
>   coh,
>   substMonadOp,
>   elimMonadOp,
>   idescOp,
>   iboxOp :
>   imapBoxOp,
>   iinductionOp,
>   argsOp,
>   schTypeOp,
>   nEOp,
>   inhEOp,
>   qElimOp,
>   recordOp,
>   labelsOp,
>   typeAtOp,
>   fstsOp,
>   atOp,
>   splitOp
>   ]

>   type DescDispatchTable = (VAL,
>                         VAL -> VAL,
>                         VAL -> VAL -> VAL,
>                         VAL -> VAL -> VAL,
>                         VAL -> VAL -> VAL)

>   type EnumDispatchTable = (VAL, VAL -> VAL -> VAL)
>
>   mkLazyEnumDef :: VAL -> EnumDispatchTable -> Either NEU VAL
>   mkLazyEnumDef arg (nilECase, consECase) = let args = arg $$ Snd in
>       case arg $$ Fst of
>           NILN   -> Right $ nilECase
>           CONSN  -> Right $ consECase (args $$ Fst) (args $$ Snd $$ Fst)
>           N t    -> Left t
>           _      -> error "mkLazyEnumDef: invalid constructor!"

>   branchesOp = Op
>     { opName   = "branches"
>     , opArity  = 2
>     , opTyTel  = bOpTy
>     , opRun    = {-bOpRun-} runOpTree $
>         oData  [ oTup $ OLam $ \_P -> ORet UNIT
>                , oTup $ \ () _E -> OLam $ \_P -> ORet $
>                  TIMES (_P $$ A ZE)
>                     (branchesOp @@ [_E, L $ "x" :. [.x. _P -$ [SU (NV x)]]])
>                ]
>     , opSimp   = \_ _ -> empty
>     } where
>         bOpTy = "e" :<: enumU :-: \e ->
>                 "p" :<: ARR (ENUMT e) SET :-: \p ->
>                 Target SET

>   switchOp = Op
>     { opName  = "switch"
>     , opArity = 4
>     , opTyTel = sOpTy
>     , opRun   = runOpTree $ {- sOpRun -- makeOpRun "switch" switchTest -}
>         OLam $ \_ ->
>         OCase (map projector [0..])
>     , opSimp  = \_ _ -> empty
>     } where
>         projector i = OLam $ \_ -> OLam $ \bs -> ORet (proj i bs)
>         proj 0 bs = bs $$ Fst
>         proj i bs = proj (i - 1) (bs $$ Snd)
>         sOpTy =
>           "e" :<: enumU :-: \e ->
>           "x" :<: ENUMT e :-: \x ->
>           "p" :<: ARR (ENUMT e) SET :-: \p ->
>           "b" :<: branchesOp @@ [e , p] :-: \b ->
>           Target (p $$ A x)

>   enumInductionOp = Op
>     {  opName = "enumInduction"
>     ,  opArity = 5
>     ,  opTyTel = eOpTy
>     ,  opRun = runOpTree $
>        oData  [  oTup $ OSet $ \ c -> OBarf
>               ,  oTup $ \ t e ->
>                  OSet $ \ c ->
>                  oLams $ \ p mz ms ->
>                  case c of
>                    Ze      -> ORet (mz $$ A t $$ A e)
>                    (Su x)  -> ORet (ms $$ A t $$ A e $$ A x $$ A
>                                            (enumInductionOp @@ [e, x, p, mz, ms]))
>               ]
>     ,  opSimp = \ _ _ -> empty
>     } where
>       eOpTy =
>         "e" :<: enumU :-: \ e ->
>         "x" :<: ENUMT e :-: \ x ->
>         "p" :<: ARR (SIGMA enumU (L $ "e" :. [.e. ENUMT (NV e)])) SET :-: \ p ->
>         "mz" :<: (PI UID $ L $ "t" :. [.t.
>                      PI enumU $ L $ "e" :. [.e.
>                          p -$ [PAIR (CONSE (NV t) (NV e)) ZE]
>                      ]]) :-: \ mz ->
>         "ms" :<: (PI UID $ L $ "t" :. [.t.
>                      PI enumU $ L $ "e" :. [.e.
>                      PI (ENUMT (NV e)) $ L $ "x" :. [.x.
>                      ARR (p -$ [PAIR (NV e) (NV x)])
>                          (p -$ [PAIR (CONSE (NV t) (NV e)) (SU (NV x))])
>                      ]]]) :-: \ ms ->
>         Target (p $$ A (PAIR e x))

>   eqGreen = Op { opName = "eqGreen"
>                , opArity = 4
>                , opTyTel =  "S" :<: SET :-: \ sS -> "s" :<: sS :-: \ s ->
>                             "T" :<: SET :-: \ tT -> "t" :<: tT :-: \ t ->
>                             Target PROP
>                , opRun = opRunEqGreen
>                , opSimp = \_ _ -> empty
>                } where
>                opty chev [y0,t0,y1,t1] = do
>                    (y0 :=>: y0v) <- chev (SET :>: y0)
>                    (t0 :=>: t0v) <- chev (y0v :>: t0)
>                    (y1 :=>: y1v) <- chev (SET :>: y1)
>                    (t1 :=>: t1v) <- chev (y1v :>: t1)
>                    return ([ y0 :=>: y0v
>                            , t0 :=>: t0v
>                            , y1 :=>: y1v
>                            , t1 :=>: t1v ]
>                           , PROP)
>                opty _  _             = throwError' "eqGreen: invalid arguments."

>   coe = Op { opName = "coe"
>            , opArity = 4
>            , opTyTel =  "S" :<: SET :-: \ sS -> "T" :<: SET :-: \ tT ->
>                         "Q" :<: PRF (EQBLUE (SET :>: sS) (SET :>: tT)) :-: \ _ ->
>                         "s" :<: sS :-: \ _ -> Target tT
>            , opRun = oprun
>            , opSimp = \ [sS, tT, _, s] r -> case s of
>                N s | equal (SET :>: (sS, tT)) r -> pure s
>                _ -> (|)
>            } where
>            oprun :: [VAL] -> Either NEU VAL
>            oprun [_S, _T, q, v] | partialEq _S _T q = Right v
>            oprun [C (Mu t0), C (Mu t1), q, s] = case halfZip (Mu (dropLabel t0)) (Mu (dropLabel t1)) of
>              Nothing -> Right $ nEOp @@ [q $$ Out, C (Mu t1)]
>              Just fxy -> coerce fxy (q $$ Out) s
>            oprun [C x,C y,q,s] = case halfZip x y of
>              Nothing  -> Right $ nEOp @@ [q $$ Out, C y]
>              Just fxy -> coerce fxy (q $$ Out) s
>            oprun [N x,y,q,s] = Left x
>            oprun [x,N y,q,s] = Left y
>            oprun vs = error ("coe: undefined for arguments"
>                                  ++ unlines (map show vs))

>   coh = Op { opName = "coh"
>            , opArity = 4
>            , opTyTel =
>                "S" :<: SET :-: \ _S -> "T" :<: SET :-: \ _T ->
>                "Q" :<: PRF (EQBLUE (SET :>: _S) (SET :>: _T)) :-: \ _Q ->
>                "s" :<: _S :-: \ s -> Target $ PRF $
>                EQBLUE (_S :>: s) (_T :>: (coe @@ [_S, _T, _Q, s]))
>            , opRun = oprun
>            , opSimp = \ [_S, _T, _, s] r ->
>                if equal (SET :>: (_S, _T)) r
>                  then pure $ P refl :$ A _S :$ A s
>                  else (|)
>            } where
>            oprun :: [VAL] -> Either NEU VAL
>            oprun [_S, _T, q, s] | partialEq _S _T q =
>              Right (pval refl $$ A _S $$ A s)
>            oprun [N x,y,q,s] = Left x
>            oprun [x,N y,q,s] = Left y
>            oprun [_S,_T,_Q,s] = Right $
>              pval cohAx $$ A _S $$ A _T $$ A _Q $$ A s
>            oprun vs = error ("coe: undefined for arguments"
>                                  ++ unlines (map show vs))

>   substMonadOp = Op
>     { opName = "substMonad"
>     , opArity = 5
>     , opTyTel =  "D" :<: desc                  :-: \ dD ->
>                  "X" :<: SET                   :-: \ xX ->
>                  "Y" :<: SET                   :-: \ yY ->
>                  "f" :<: ARR xX (MONAD dD yY)  :-: \ f ->
>                  "t" :<: MONAD dD xX           :-: \ t ->
>                  Target $ MONAD dD yY
>     , opRun = substMonadOpRun
>     , opSimp = substMonadOpSimp
>     } where
>       substMonadOpRun :: [VAL] -> Either NEU VAL
>       substMonadOpRun [dD, xX, yY, f, COMPOSITE ts] = Right . COMPOSITE $
>         mapOp @@ [  dD, MONAD dD xX, MONAD dD yY,
>                     L $ "t" :. [.t. N $
>                     substMonadOp :@ [  dD -$ [], xX -$ [], yY -$ []
>                                     ,  f -$ [], NV t] ] ,
>                     ts]
>       substMonadOpRun [d, x, y, f, RETURN z]  = Right $ f $$ A z
>       substMonadOpRun [d, x, y, f, N t]    = Left t
>
>       substMonadOpSimp :: Alternative m => [VAL] -> NameSupply -> m NEU
>       substMonadOpSimp [d, x, y, f, N t] r
>         | equal (SET :>: (x, y)) r &&
>           equal (ARR x (MONAD d x) :>: (f, ret)) r = pure t
>         where
>           ret = L ("x" :. [.x. RETURN (NV x)])
>       substMonadOpSimp [d, y, z, f, N (sOp :@ [_, x, _, g, N t])] r
>         | sOp == substMonadOp = pure $ substMonadOp :@ [d, x, z, comp, N t]
>         where  comp = L $ "x" :. [.x. N $
>                         substMonadOp :@ [ d -$ [], y -$ [], z -$ []
>                                         , f -$ [], g -$ [ NV x ] ] ]
>       substMonadOpSimp _ _ = empty

>   elimMonadOp :: Op
>   elimMonadOp = Op
>     { opName = "elimMonad"
>     , opArity = 6
>     , opTyTel =  "D" :<: desc                       :-: \ dD ->
>                  "X" :<: SET                        :-: \ xX ->
>                  "t" :<: MONAD dD xX                :-: \ t ->
>                  "P" :<: ARR (MONAD dD xX) SET      :-: \ pP ->
>                  "c" :<: (PI (descOp @@ [dD, MONAD dD xX]) $ L $ "ts" :. [.ts.
>                            ARR (N (boxOp :@ [  dD -$ []
>                                             ,  MONAD (dD -$ []) (xX -$ [])
>                                             ,  pP -$ [] , NV ts]))
>                             (pP -$ [COMPOSITE (NV ts) ])])  :-: \ _ ->
>                  "v" :<: (PI xX $ L $ "x" :. [.x. pP -$ [ RETURN (NV x) ] ])       :-: \ _ ->
>                  Target $ pP $$ A t
>     , opRun = elimMonadOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       elimMonadOpRun :: [VAL] -> Either NEU VAL
>       elimMonadOpRun [d,x,COMPOSITE ts,bp,mc,mv] = Right $
>         mc $$ A ts $$ A (mapBoxOp @@ [d, MONAD d x, bp,
>           L $ "t" :. [.t. N $ elimMonadOp :@ [  d -$ [], x -$ []
>                                              ,  NV t , bp -$ []
>                                              ,  mc -$ [], mv -$ [] ] ] ,
>           ts])
>       elimMonadOpRun [d,x,RETURN z,bp,mc,mv] = Right $ mv $$ A z
>       elimMonadOpRun [_,_,N n,_,_,_] = Left n

>   idescOp :: Op
>   idescOp = Op
>     { opName = "idesc"
>     , opArity = 3
>     , opTyTel = idOpTy
>     , opRun = runOpTree $ OLam $ \_I -> oData {- idOpRun -}
>         [ {-VAR-} oTup $ \i -> OLam $ \_P -> ORet $ _P $$ A i
>         , {-CONST-} oTup $ \_A -> OLam $ \_P -> ORet _A
>         , {-PI-} oTup $ \_S _T -> OLam $ \_P -> ORet $
>                    PI _S $ L $ "s" :. [.s. N $
>                      idescOp :@ [ _I -$ [] , _T -$ [NV s], _P -$ [] ]]
>         , {-FPI-} oTup $ \_E _Df -> OLam $ \_P -> ORet $
>                     branchesOp @@
>                       [  _E
>                       ,  (L $ "e" :. [.e. N $
>                             idescOp :@  [  _I -$ []
>                                         ,  _Df -$ [NV e]
>                                         ,  _P -$ []
>                                         ]])
>                       ]
>         , {-SIGMA-} oTup $ \_S _T -> OLam $ \_P -> ORet $
>                       SIGMA _S $ L $ (fortran _T) :. [.s. N $
>                         idescOp :@ [ _I -$ [] , _T -$ [NV s], _P -$ [] ]]
>         , {-FSIGMA-} oTup $ \_E _Ds -> OLam $ \_P -> ORet $
>                        SIGMA (ENUMT _E) (L $ (fortran _Ds) :. [.s. N $
>                          idescOp :@ [ _I -$ []
>                                     , N $ switchOp :@
>                                             [ _E -$ []
>                                             , NV s
>                                             , LK (idesc -$ [ _I -$ []])
>                                             , _Ds -$ [] ]
>                                     , _P -$ [] ] ])
>         , {-PROD-} oTup $ \u _D _D' -> OLam $ \_P -> ORet $
>                      SIGMA (idescOp @@ [_I, _D, _P]) $ L $ (unTag u) :.
>                         (N (idescOp :@ [_I -$ [], _D' -$ [], _P -$ []]))
>         ]
>     , opSimp = \_ _ -> empty
>     } where
>       idOpTy =
>        "I" :<: SET :-: \iI ->
>        "d" :<: (idesc $$ A iI) :-: \d ->
>        "X" :<: ARR iI SET :-: \x ->
>        Target SET

>   iboxOp :: Op
>   iboxOp = Op
>     { opName = "ibox"
>     , opArity = 4
>     , opTyTel = iboxOpTy
>     , opRun = runOpTree $ OLam $ \_I -> oData  {- iboxOpRun -}
>         [ {-VAR-} oTup $ \i -> oLams $ \() v -> ORet $
>                     IVAR (PAIR i v)
>         , {-CONST-} oTup $ \() -> oLams $ \() () -> ORet $
>                        ICONST (PRF TRIVIAL)
>         , {-PI-} oTup $ \_S _T -> oLams $ \_P f -> ORet $
>                    IPI _S (L $ "s" :. [.s. N $
>                      iboxOp :@  [  _I -$ [], _T -$ [NV s]
>                                 ,  _P -$ [], f -$ [NV s]] ])
>         , {-FPI-} oTup $ \_E _Df -> oLams $ \_P v -> ORet $
>                     IFPI _E (L $ "e" :. [.e. N $
>                       iboxOp :@  [  _I -$ [] , _Df -$ [NV e], _P -$ []
>                                  ,  N $ switchOp :@
>                                           [  _E -$ [] , NV e
>                                           ,  L $ "f" :. [.f. N $
>                                                idescOp :@  [  _I -$ []
>                                                            ,  _Df -$ [NV f]
>                                                            , _P -$ [] ] ]
>                                           ,  v -$ []]]])
>         , {-SIGMA-} oTup $ \() _T -> OLam $ \_P -> OPr $ oLams $ \s d -> ORet $
>                       iboxOp @@ [_I, _T $$ A s, _P, d]
>         , {-FSIGMA-} oTup $ \_E _Ds -> OLam $ \_P -> OPr $ oLams $ \e d -> ORet $
>             iboxOp @@ [_I
>                       , switchOp @@ [ _E
>                                     , e
>                                     , LK (idesc $$ A _I)
>                                     , _Ds ]
>                       , _P
>                       , d ]
>         , {-PROD-} oTup $ \u _D _D' -> OLam $ \_P -> OPr $ oLams $ \d d' -> ORet $
>             IPROD  (TAG (unTag u ++ "h")) (iboxOp @@ [_I, _D, _P, d])
>                     (iboxOp @@ [_I, _D', _P, d'])
>         ]
>     , opSimp = \_ _ -> empty
>     } where
>       iboxOpTy =
>         "I" :<: SET                        :-: \ _I ->
>         "D" :<: (idesc $$ A _I)  :-: \ _D ->
>         "P" :<: ARR _I SET                 :-: \ _P ->
>         "v" :<: idescOp @@ [_I,_D,_P]      :-: \v ->
>         Target $ idesc $$ A (SIGMA _I (L $ "i" :. [.i. _P -$ [NV i]]))

>   imapBoxOp :: Op
>   imapBoxOp = Op
>     { opName = "imapBox"
>     , opArity = 6
>     , opTyTel = imapBoxOpTy
>     , opRun = runOpTree $ OLam $ \_I -> oData {- imapBoxOpRun -}
>         [ {-VAR-} oTup $ \i -> oLams $ \() () p v -> ORet $ p $$ A (PAIR i v)
>         , {-CONST-} oTup $ \() -> oLams $ \() () () () -> ORet $ VOID
>         , {-PI-} oTup $ \() _T -> oLams $ \_X _P p f -> ORet $
>             L $ "s" :. [.s. N $
>               imapBoxOp :@  [  _I -$ [], _T -$ [NV s]
>                             ,  _X -$ [] ,_P -$ [], p -$ [], f -$ [NV s] ] ]
>         , {-FPI-} oTup $ \() _Df -> oLams $ \_X _P p v -> ORet $
>             L $ "s" :. [.s. N $
>               imapBoxOp :@  [  _I -$ [], _Df -$ [NV s]
>                             ,  _X -$ [] ,_P -$ [], p -$ [], v -$ [NV s] ] ]
>         , {-SIGMA-} oTup $ \() _T -> oLams $ \_X _P p -> OPr $ oLams $ \s d -> ORet $
>             imapBoxOp @@ [  _I, _T $$ A s, _X, _P, p, d]
>         , {-FSIGMA-} oTup $ \_E _Ds -> oLams $ \_X _P p -> OPr $ oLams $ \e d -> ORet $
>             imapBoxOp @@ [  _I
>                          ,  switchOp @@ [  _E, e
>                                         ,  LK (idesc $$ A _I)
>                                         ,  _Ds
>                                         ]
>                          ,  _X, _P, p, d ]
>         , {-PROD-} oTup $ \() _D _D' -> oLams $ \_X _P p -> OPr $ oLams $ \d d' -> ORet $
>             PAIR (imapBoxOp @@ [_I, _D, _X, _P, p, d])
>                   (imapBoxOp @@ [_I, _D', _X, _P, p, d'])
>         ]
>     , opSimp = \_ _ -> empty
>     } where
>       imapBoxOpTy =
>         "I" :<: SET :-: \_I ->
>         "D" :<: (idesc $$ A _I) :-: \ _D ->
>         "X" :<: ARR _I SET :-: \ _X ->
>         let _IX = SIGMA _I (L $ "i" :. [.i. _X -$ [NV i] ]) in
>         "P" :<: ARR _IX SET :-: \ _P ->
>         "p" :<: (PI _IX $ L $ "ix" :. [.ix. _P -$ [ NV ix ] ] ) :-: \ _ ->
>         "v" :<: (idescOp @@ [_I,_D,_X]) :-: \v ->
>          Target (idescOp @@ [_IX, iboxOp @@ [_I,_D,_X,v], _P])

>   iinductionOpMethodType _I _D _P =
>       PI _I $ L $ "i" :. [.i.
>        let _It = _I -$ []
>            mud = L $ "j" :. [.j. IMU Nothing _It (_D -$ []) (NV j) ]
>        in PI (N (idescOp :@ [ _It, _D -$ [ NV i ], mud])) $ L $ "x" :. [.x.
>            ARR (N (idescOp :@ [ SIGMA _It mud
>                               , N (iboxOp :@ [_It, _D -$ [ NV i ], mud, NV x])
>                               , _P -$ [] ]))
>             (_P -$ [ PAIR (NV i) (CON (NV x)) ]) ] ]

>   iinductionOp :: Op
>   iinductionOp = Op
>     { opName = "iinduction"
>     , opArity = 6
>     , opTyTel = iinductionOpTy
>     , opRun = runOpTree $ oLams $ \_I _D i -> OCon $ oLams $ \v _P p -> ORet $
>         p $$ A i $$ A v
>           $$ A (imapBoxOp @@ [ _I, _D $$ A i
>                              , (L $ "i" :. [.i.
>                                  IMU Nothing (_I -$ []) (_D -$ []) (NV i)])
>                              , _P
>                              , L $ "ix" :. [.ix. N $
>                                 iinductionOp :@
>                                   [ _I -$ [], _D -$ []
>                                   , N (V ix :$ Fst), N (V ix :$ Snd)
>                                   , _P -$ [], p -$ [] ] ]
>                              , v])
>     , opSimp = \_ _ -> empty
>     } where
>       iinductionOpTy =
>         "I" :<: SET :-: \_I ->
>         "D" :<: ARR _I (idesc $$ A _I) :-: \_D ->
>         "i" :<: _I :-: \i ->
>         "v" :<: IMU Nothing _I _D i :-: \v ->
>         "P" :<: (ARR (SIGMA _I (L $ "i" :. [.i.
>                   IMU Nothing (_I -$ []) (_D -$ []) (NV i) ])) SET) :-: \_P ->
>         "p" :<: (iinductionOpMethodType _I _D _P) :-: \p ->
>         Target (_P $$ A (PAIR i v))

<   callOp = Op
<     { opName = "call"
<     , opArity = 3
<     , opTy = callOpTy
<     , opRun = callOpRun
<     , opSimp = callOpSimp
<     } where
<       callOpTy chev [ty, lbl, tm] = do
<            tytv@(ty :=>: tyv) <- chev (SET :>: ty)
<            lbltv@(lbl :=>: lblv) <- chev (tytv :>: lbl)
<            tmtv@(tm :=>: tmv) <- chev (LABEL lbltv tytv :>: tm)
<            return ([tytv, lbltv, tmtv], tyv)

<       callOpRun :: [VAL] -> Either NEU VAL
<       callOpRun [ty, lbl, LRET t] = Right t
<       callOpRun [ty, lbl, N t] = Left t

<       callOpSimp :: Alternative m => [VAL] -> NameSupply -> m NEU
<       callOpSimp _ _ = empty

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

>   nEOp = Op { opName = "naughtE"
>             , opArity = 2
>             , opTyTel =  "z" :<: PRF ABSURD :-: \ _ ->
>                          "X" :<: SET :-: \ xX -> Target xX
>             , opRun = runOpTree $ OCon $ OBarf
>             , opSimp = \_ _ -> empty
>             }
>   inhEOp = Op { opName = "inh"
>               , opArity = 4
>               , opTyTel = "S" :<: SET :-: \ ty ->
>                           "p" :<: PRF (INH ty) :-: \ p ->
>                           "P" :<: IMP (PRF (INH ty)) PROP :-: \ pred ->
>                           "m" :<: PI ty (L $ "s" :. [.t.
>                                            pred -$ [ WIT (NV t) ] ]) :-: \ _ ->
>                           Target (PRF (pred $$ A p))
>               , opRun = \[_,p,_,m] -> case p of
>                                         WIT t -> Right $ m $$ A t
>                                         N n   -> Left n
>               , opSimp = \_ _ -> empty
>               }

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

>   recordOp = Op
>     { opName   = "Record"
>     , opArity  = 1
>     , opTyTel  = recordOpTy
>     , opRun    = recordOpRun
>     , opSimp   = \_ _ -> empty
>     } where
>         recordOpTy = "sig" :<: RSIG :-: \sig ->
>                      Target SET
>         recordOpRun :: [VAL] -> Either NEU VAL
>         recordOpRun [REMPTY]           = Right UNIT
>         recordOpRun [RCONS sig id ty]  = Right $ SIGMA (recordOp @@ [sig]) ty
>         recordOpRun [N x]              = Left x
>
>   labelsOp = Op
>     { opName   = "labels"
>     , opArity  = 1
>     , opTyTel  = labelsOpTy
>     , opRun    = labelsOpRun
>     , opSimp   = \_ _ -> empty
>     } where
>         labelsOpTy =  "sig" :<: RSIG :-: \sig ->
>                       Target enumU
>         labelsOpRun :: [VAL] -> Either NEU VAL
>         labelsOpRun [REMPTY]           = Right NILE
>         labelsOpRun [RCONS sig id ty]  = Right $ CONSE id (labelsOp @@ [sig])
>         labelsOpRun [N x]              = Left x
>
>   typeAtOp = Op
>     { opName   = "typeAt"
>     , opArity  = 2
>     , opTyTel  = typeAtOpTy
>     , opRun    = typeAtOpRun
>     , opSimp   = \_ _ -> empty
>     } where
>         typeAtOpTy =  "sig" :<: RSIG :-: \sig ->
>                       "labels" :<: ENUMT (labelsOp @@ [sig]) :-: \_ ->
>                       Target $ SIGMA RSIG  (L $ "S" :. [.s.
>                                            ARR (N $ recordOp :@ [NV s]) SET])
>         typeAtOpRun :: [VAL] -> Either NEU VAL
>         typeAtOpRun [REMPTY, _]              =
>             error "typeAt: impossible call on Empty"
>         typeAtOpRun [RCONS sig id ty, ZE]    = Right $ PAIR sig ty
>         typeAtOpRun [RCONS sig id ty, SU n]  = Right $ typeAtOp @@ [ sig, n ]
>         typeAtOpRun [_,N x]                 = Left x
>
>   fstsOp = Op
>     { opName   = "fsts"
>     , opArity  = 3
>     , opTyTel  = fstsOpTy
>     , opRun    = fstsOpRun
>     , opSimp   = \_ _ -> empty
>     } where
>         fstsOpTy =  "sig" :<: RSIG :-: \sig ->
>                     "labels" :<: ENUMT (labelsOp @@ [sig]) :-: \l ->
>                     "rec" :<: recordOp @@ [sig] :-: \_ ->
>                       Target $ recordOp @@ [ typeAtOp @@ [ sig, l ] $$ Fst ]
>         fstsOpRun :: [VAL] -> Either NEU VAL
>         fstsOpRun [REMPTY, _, _]              =
>             error "fsts: impossible call on Empty"
>         fstsOpRun [RCONS sig id ty, ZE, x]    =
>             Right $ x $$ Fst
>         fstsOpRun [RCONS sig id ty, SU n, x]  =
>             Right $ fstsOp @@ [sig, n, x $$ Fst]
>         fstsOpRun [_, N x, _]                 = Left x
>
>   atOp = Op
>     { opName   = "at"
>     , opArity  = 3
>     , opTyTel  = atOpTy
>     , opRun    = atOpRun
>     , opSimp   = \_ _ -> empty
>     } where
>         atOpTy =  "sig" :<: RSIG :-: \sig ->
>                   "labels" :<: ENUMT (labelsOp @@ [sig]) :-: \l ->
>                   "rec" :<: recordOp @@ [sig] :-: \rec ->
>                    Target $ typeAtOp @@ [ sig, l ]
>                               $$ Snd
>                               $$ A (fstsOp @@ [ sig, l, rec])
>         atOpRun :: [VAL] -> Either NEU VAL
>         atOpRun [REMPTY, _, _]              =
>             error "at: impossible call on Empty"
>         atOpRun [RCONS sig id ty, ZE, x]    =
>             Right $ x $$ Snd
>         atOpRun [RCONS sig id ty, SU n, x]  =
>             Right $ atOp @@ [sig, n, x $$ Fst]
>         atOpRun [_, N x, _]                 = Left x

>   splitOp = Op
>     { opName = "split" , opArity = 5
>     , opTyTel =  "A"   :<: SET                          :-: \ aA ->
>                  "B"   :<: ARR aA SET                   :-: \ bB ->
>                  "ab"  :<: SIGMA aA bB                  :-: \ ab ->
>                  "P"   :<: ARR (SIGMA aA bB) SET        :-: \ pP ->
>                  "p"   :<: (
>                    PI aA $ L $ "a" :. [.a.
>                     PI (bB -$ [ NV a ]) $ L $ "b" :. [.b.
>                      pP -$ [ PAIR (NV a) (NV b) ] ] ])  :-: \ p ->
>                  Target $ pP $$ A ab
>     , opRun = runOpTree $
>         oLams $ \ () () ab () p -> ORet $ p $$ A (ab $$ Fst) $$ A (ab $$ Snd)
>     , opSimp = \_ _ -> empty
>     }

>   descConstructors :: Tm {In, p} x
>   descConstructors =  CONSE (TAG "idD")
>                            (CONSE (TAG "constD")
>                            (CONSE (TAG "sumD")
>                            (CONSE (TAG "prodD")
>                            (CONSE (TAG "sigmaD")
>                            (CONSE (TAG "piD")
>                             NILE)))))

>   descBranches :: Tm {In, p} x
>   descBranches = (PAIR (CONSTD UNIT)
>                     (PAIR (SIGMAD SET (L $ K $ CONSTD UNIT))
>                     (PAIR (SIGMAD enumU (L $ "E" :. [._E.
>                                       (PRODD (TAG "T") (PID (ENUMT (NV _E)) (LK IDD))
>                                              (CONSTD UNIT))]))
>                     (PAIR (SIGMAD UID (L $ "u" :. PRODD (TAG "C") IDD (PRODD (TAG "D") IDD (CONSTD UNIT))))
>                     (PAIR (SIGMAD SET (L $ "S" :. [._S.
>                                       (PRODD (TAG "T") (PID (NV _S) (LK IDD))
>                                              (CONSTD UNIT))]))
>                     (PAIR (SIGMAD SET (L $ "S" :. [._S.
>                                       (PRODD (TAG "T") (PID (NV _S) (LK IDD))
>                                              (CONSTD UNIT))]))
>                      VOID))))))

>   descD :: Tm {In, p} x
>   descD = SUMD descConstructors
>                (L $ "c" :. [.c. N $
>                    switchDOp :@ [ descConstructors , descBranches , NV c] ])

>   desc :: Tm {In, p} x
>   desc = MU (Just (ANCHOR (TAG "Desc") SET ALLOWEDEPSILON)) descD
>
>   descREF :: REF
>   descREF = [("Primitive", 0), ("Desc", 0)] := DEFN desc :<: SET
>
>   descDREF :: REF
>   descDREF = [("Primitive", 0), ("DescD", 0)] := DEFN descD :<: desc

>   descConstructorsREF :: REF
>   descConstructorsREF = [("Primitive", 0), ("DescConstructors", 0)] :=
>       DEFN descConstructors :<: enumU

>   descBranchesREF :: REF
>   descBranchesREF = [("Primitive", 0), ("DescBranches", 0)] :=
>       DEFN descBranches :<: branchesOp @@ [descConstructors, LK desc]

>   enumConstructors :: Tm {In, p} x
>   enumConstructors = CONSE (TAG "nil") (CONSE (TAG "cons") NILE)

>   enumBranches :: Tm {In, p} x
>   enumBranches =
>       PAIR (CONSTD UNIT)
>           (PAIR (SIGMAD UID (L $ "t" :. (PRODD (TAG "E") IDD (CONSTD UNIT))))
>               VOID)

>   enumD :: Tm {In, p} x
>   enumD = SIGMAD  (ENUMT enumConstructors)
>                     (L $ "c" :. [.c. N $
>                         switchDOp :@ [ enumConstructors , enumBranches , NV c] ])

>   enumU :: Tm {In, p} x
>   enumU = MU (Just (ANCHOR (TAG "EnumU") SET ALLOWEDEPSILON)) enumD

>   enumREF :: REF
>   enumREF = [("Primitive", 0), ("EnumU", 0)] := DEFN enumU :<: SET

>   enumDREF :: REF
>   enumDREF = [("Primitive", 0), ("EnumD", 0)] := DEFN enumD :<: desc

>   enumConstructorsREF :: REF
>   enumConstructorsREF = [("Primitive", 0), ("EnumConstructors", 0)] :=
>       DEFN enumConstructors :<: enumU

>   enumBranchesREF :: REF
>   enumBranchesREF = [("Primitive", 0), ("EnumBranches", 0)] :=
>       DEFN enumBranches :<:
>           branchesOp @@ [enumConstructors, LK desc]

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

>   inIDesc :: VAL
>   inIDesc = L $ "I" :. [._I. LK $ IFSIGMA constructors (cases (NV _I)) ]

>   constructors = (CONSE (TAG "varD")
>                  (CONSE (TAG "constD")
>                  (CONSE (TAG "piD")
>                   (CONSE (TAG "fpiD")
>                    (CONSE (TAG "sigmaD")
>                     (CONSE (TAG "fsigmaD")
>                      (CONSE (TAG "prodD")
>                       NILE)))))))

>   cases :: INTM -> INTM
>   cases _I =
>    {- varD: -}    (PAIR (ISIGMA _I (LK $ ICONST UNIT))
>    {- constD: -}  (PAIR (ISIGMA SET (LK $ ICONST UNIT))
>    {- piD: -}     (PAIR (ISIGMA SET (L $ "S" :. [._S.
>                     (IPROD (TAG "T") (IPI (NV _S) (LK $ IVAR VOID))
>                            (ICONST UNIT))]))
>    {- fpiD: -}    (PAIR (ISIGMA (enumU -$ []) (L $ "E" :. [._E.
>                     (IPROD (TAG "T") (IPI (ENUMT (NV _E)) (LK $ IVAR VOID))
>                            (ICONST UNIT))]))
>    {- sigmaD: -}  (PAIR (ISIGMA SET (L $ "S" :. [._S.
>                     (IPROD (TAG "T") (IPI (NV _S) (LK $ IVAR VOID))
>                            (ICONST UNIT))]))
>    {- fsigmaD: -} (PAIR (ISIGMA (enumU -$ []) (L $ "E" :. [._E.
>                     (IPROD (TAG "T") (IFPI (NV _E) (LK $ IVAR VOID))
>                            (ICONST UNIT))]))
>    {- prodD: -}   (PAIR (ISIGMA UID (L $ "u" :. (IPROD (TAG "C") (IVAR VOID) (IPROD (TAG "D") (IVAR VOID) (ICONST UNIT)))))
>                     VOID)))))))

>   idescFakeREF :: REF
>   idescFakeREF = [("Primitive", 0), ("IDesc", 0)]
>                    := (FAKE :<: ARR SET (ARR UNIT SET))
>   idesc :: VAL
>   idesc = L $ "I" :. [._I.
>             IMU (Just (L $ "i" :. [.i. ANCHOR  (TAG "IDesc")
>                                                (ARR SET SET)
>                                                (ALLOWEDCONS  SET
>                                                              (LK SET)
>                                                              (N (P refl :$ A SET :$ A (ARR SET SET)))
>                                                              (NV _I)
>                                                              ALLOWEDEPSILON)]))
>                  UNIT (inIDesc -$ [ NV _I]) VOID ]
>
>   idescREF :: REF
>   idescREF = [("Primitive", 0), ("IDesc", 0)]
>                := (DEFN idesc :<: ARR SET SET)
>
>   idescDREF :: REF
>   idescDREF = [("Primitive", 0), ("IDescD", 0)]
>                 := (DEFN inIDesc
>                      :<: ARR SET (ARR UNIT (idesc $$ A UNIT)))

>   idescConstREF :: REF
>   idescConstREF = [("Primitive", 0), ("IDescConstructors", 0)]
>                    := (DEFN constructors :<: enumU)
>
>   idescBranchesREF :: REF
>   idescBranchesREF = [("Primitive", 0), ("IDescBranches", 0)]
>                       := (DEFN (L $ "I" :. [._I. cases (NV _I)])) :<:
>                            PI SET (L $ "I" :. [._I.
>                              N $ branchesOp :@ [ constructors,
>                                                  LK $ N (P idescREF :$ A UNIT)]])

>   sumilike :: VAL -> VAL -> Maybe (VAL, VAL -> VAL)
>   sumilike _I (IFSIGMA e b)  =
>       Just (e, \t -> switchOp @@ [ e , t , LK (idesc $$ A _I), b ])
>   sumilike _ _               = Nothing

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

The list of |primitives| includes axioms and fundamental definitions provided
by the |Primitives| aspect, plus a reference corresponding to each operator.

> primitives :: [(String, REF)]
> primitives = map (\op -> (opName op, mkRef op)) operators ++ (
>     import <- Primitives
>     [])
>   where
>     mkRef :: Op -> REF
>     mkRef op = [("Operators",0),(opName op,0)] := (DEFN opEta :<: opTy)
>       where
>         opTy = pity (opTyTel op) (((B0 :<  ("Operators",0) :<
>                                            (opName op,0) :<
>                                            ("opTy",0)), 0) :: NameSupply)
>         ari = opArity op
>         args = map NV [(ari-1),(ari-2)..0]
>         names = take (ari-1) (map (\x -> [x]) ['b'..])
>         opEta = L $ "a" :. Prelude.foldr (\s x -> L (s :. x)) (N $ op :@ args) names
>

We can look up the primitive reference corresponding to an operator using
|lookupOpRef|. This ensures we maintain sharing of these references.

> lookupOpRef :: Op -> REF
> lookupOpRef op = case lookup (opName op) primitives of
>     Just ref  -> ref
>     Nothing   -> error $ "lookupOpRef: missing operator primitive " ++ show op

> pity :: NameSupplier m => TEL TY -> m TY
> pity (Target t)       = return t
> pity (x :<: s :-: t)  = do
>   freshRef  (x :<: error "pity': type undefined")
>             (\xref -> do
>                t <- pity $ t (pval xref)
>                t <- bquote (B0 :< xref) t
>                return $ PI s (L $ x :. t))
