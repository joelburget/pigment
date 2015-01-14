Observational Equality
======================

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts, PatternGuards,
>     PatternSynonyms #-}

> module Evidences.PropositionalEquality where

> import Control.Applicative
> import Kit.MissingLibrary
> import Evidences.Tm
> import Evidences.Eval
> import Evidences.Operators
> import Evidences.TypeChecker

Let's have some observational equality, now!
@altenkirch_mcbride_swierstra:obs_equality

The `eqGreen` operator, defined in section [sec:Features.Equality],
computes the proposition that two values are equal if their containing
sets are equal. We write `<->` for application of this operator.

> (<->) :: (TY :>: VAL) -> (TY :>: VAL) -> VAL
> (y0 :>: t0) <-> (y1 :>: t1) = eqGreen @@ [y0,t0,y1,t1]

> (<:-:>) :: (INTM :>: INTM) -> (INTM :>: INTM) -> INTM
> (y0 :>: t0) <:-:> (y1 :>: t1) = N $ eqGreen :@ [y0,t0,y1,t1]

We define the computational behaviour of the `eqGreen` operator as
follows,

> opRunEqGreen :: [VAL] -> Either NEU VAL
> opRunEqGreen [PROP,t1,PROP,t2] = Right $ AND (IMP t1 t2) (IMP t2 t1)
> opRunEqGreen [PRF _,_,PRF _,_] = Right TRIVIAL
> opRunEqGreen [UNIT,_,UNIT,_] = Right TRIVIAL
> opRunEqGreen [SIGMA s1 t1,p1,SIGMA s2 t2,p2] = Right $
>   AND (eqGreen @@ [s1,p1 $$ Fst,s2,p2 $$ Fst])
>       (eqGreen @@ [t1 $$ A (p1 $$ Fst),p1 $$ Snd,t2 $$ A (p2 $$ Fst),p2 $$ Snd])
> opRunEqGreen [QUOTIENT a r _, CLASS x, QUOTIENT b s _, CLASS y] =
>   Right $ ALL b $ L $ "x2" :. [.x2.
>             IMP (EQBLUE ((a -$ []) :>: (x -$ [])) ((b -$ []) :>: NV x2))
>                 (s -$ [NV x2 , y -$ [] ]) ]
> opRunEqGreen [QUOTIENT a r _, N x, QUOTIENT b s _, _]   = Left x
> opRunEqGreen [QUOTIENT a r _, _,   QUOTIENT b s _, N y] = Left y
> opRunEqGreen [UID,TAG s1,UID,TAG s2] | s1 == s2 = Right $ TRIVIAL
> opRunEqGreen [UID,TAG _,UID,TAG _] = Right $ ABSURD
> opRunEqGreen [C (Pi sS1 tT1), f1, C (Pi sS2 tT2), f2] = Right $
>   ALL sS1 $ L $ "s1" :.  [.s1.
>    ALL (sS2 -$ []) $ L $ "s2" :. [.s2.
>     IMP  (EQBLUE ((sS1 -$ []) :>: NV s1) ((sS2 -$ []) :>: NV s2)) $
>      (tT1 -$ [ NV s1 ] :>: f1 -$ [ NV s1 ])
>        <:-:> (tT2 -$ [ NV s2 ] :>: f2 -$ [ NV s2 ]) ] ]
> opRunEqGreen [SET, PI sS1 tT1, SET, PI sS2 tT2] = Right $
>    AND  ((SET :>: sS2) <-> (SET :>: sS1)) $
>          ALL sS2 $ L $ "s2" :. [.s2.
>           ALL (sS1 -$ []) $ L $ "s1" :. [.s1.
>            IMP  (EQBLUE ((sS2 -$ []) :>: NV s2) ((sS1 -$ []) :>: NV s1)) $
>             (SET :>: (tT1 -$ [ NV s1 ])) <:-:> (SET :>: (tT2 -$ [ NV s2 ])) ] ]
> opRunEqGreen [SET, C (Mu (_ :?=: Id t0)), SET, C (Mu (_ :?=: Id t1))] =
>     opRunEqGreen [desc, t0, desc, t1]

Unless overridden by a feature or preceding case, we determine equality
of canonical values in canonical sets by labelling subterms of the
values with their types, half-zipping them together (ensuring that the
head constructors are identical) and requiring that the subterms are
equal.

> opRunEqGreen [C ty0, C t0, C ty1, C t1] =
>     case halfZip (fmap termOf t0') (fmap termOf t1') of
>         Nothing  -> Right ABSURD
>         Just x   -> Right $ mkEqConj (trail x)
>   where
>     Right t0'  = canTy (\tx@(t :>: x) -> Right (tx :=>: x)) (ty0 :>: t0)
>     Right t1'  = canTy (\tx@(t :>: x) -> Right (tx :=>: x)) (ty1 :>: t1)

If we are trying to equate a function and a canonical value, we don't
have much hope.

> opRunEqGreen [_,     L _,   _,     C _   ] = Right ABSURD
> opRunEqGreen [_,     C _,   _,     L _   ] = Right ABSURD

If one of the arguments is neutral, we blame it for being unable to
compute.

> opRunEqGreen [C _,   N t0,  C _,   _     ] = Left t0
> opRunEqGreen [C _,   _,     C _,   N t1  ] = Left t1
> opRunEqGreen [N y0,  _,     _,     _     ] = Left y0
> opRunEqGreen [_,     _,     N y1,  _     ] = Left y1

Otherwise, something has gone horribly wrong.

> opRunEqGreen as = error $ "opRunEqGreen: unmatched " ++ show as

The `mkEqConj` function builds a conjunction of `eqGreen` propositions
by folding over a list. It is uniformly structural for canonical terms,
ignoring contravariance. Therefore, this requires a special case for
`Pi` in `opRunEqGreen`.

> mkEqConj :: [(TY :>: VAL,TY :>: VAL)] -> VAL
> mkEqConj ((tt0, tt1) : [])  = tt0 <-> tt1
> mkEqConj ((tt0, tt1) : xs)  = AND (tt0 <-> tt1) (mkEqConj xs)
> mkEqConj []                 = TRIVIAL

The `coeh` function takes two types, a proof that they are equal and a
value in the first type; it produces a value in the second type and a
proof that it is equal to the original value. If the sets are
definitinoally equal then this is easy, otherwise it applies `coe` to
the value and uses the coherence axiom `coh` to produce the proof.

> coeh :: TY -> TY -> VAL -> VAL -> (VAL, VAL)
> coeh s t q v | partialEq s t q  = (v, pval refl $$ A s $$ A v)
> coeh s t q v = (  coe @@ [s , t , q , v]
>                ,  coh @@ [s , t , q , v])
> coehin :: TY -> TY -> VAL -> INTM -> (INTM, INTM)
> coehin s t q v | partialEq s t q  = (v, pval refl -$ [ s -$ [] , v ])
> coehin s t q v = (  N $ coe :@ [s -$ [], t -$ [], q -$ [], v]
>                  ,  N $ coh :@ [s -$ [], t -$ [], q -$ [], v])

The `coerce` function transports values between equal canonical sets.
Given two sets built from the same canonical constructor (represented as
`Can (VAL, VAL)`, a proof of their equality and an element of the first
set, it will try to return `Right v` where `v` is an element of the
second set. If computation is blocked by a neutral value `n`, it will
return `Left n`.

Features must extend this definition using the `Coerce` aspect for every
canonical set-former they introduce. They must handle coercions between
all canonical inhabitants of such sets, but need not deal with neutral
inhabitants. To ensure we can add arbitrary consistent axioms to the
system, they should not inspect the proof, but may eliminate it with
`naughtE` if asked to coerce between incompatible sets.

> coerce :: (Can (VAL,VAL)) -> VAL -> VAL -> Either NEU VAL
> coerce Set q x = Right x
> coerce (Pi (sS1, sS2) (tT1, tT2)) q f1 =
>   Right . L $ (fortran tT2) :. [.s2. N $
>     let  (s1, sq) = coehin sS2 sS1 (CON $ q $$ Fst) (NV s2)
>          t1 = f1 -$ [ s1 ]
>     in   coe :@ [  tT1 -$ [ s1 ], tT2 -$ [ NV s2 ]
>                 ,  CON $ (q $$ Snd) -$ [ NV s2 , s1 , sq ] , t1 ] ]
> coerce (Mu (Just (l0,l1) :?=: Id (d0,d1))) q (CON x) =
>   let typ = ARR desc (ARR ANCHORS SET)
>       vap = L $ "d" :. [.d. L $ "l" :. [.l. N $
>               descOp :@ [NV d,MU (Just $ NV l) (NV d)] ] ]
>   in Right . CON $
>     coe @@ [ descOp @@ [ d0 , MU (Just l0) d0 ]
>            , descOp @@ [ d1 , MU (Just l1) d1 ]
>            , CON $ pval refl $$ A typ $$ A vap $$ Out
>                              $$ A d0 $$ A d1 $$ A (CON $ q $$ Snd)
>                              $$ A l0 $$ A l1 $$ A (CON $ q $$ Fst)
>            , x ]
> coerce (Mu (Nothing :?=: Id (d0,d1))) q (CON x) =
>   let typ = ARR desc SET
>       vap = L $ "d" :. [.d. N $
>               descOp :@ [NV d,MU Nothing (NV d)] ]
>   in Right . CON $
>     coe @@ [ descOp @@ [ d0 , MU Nothing d0 ]
>            , descOp @@ [ d1 , MU Nothing d1 ]
>            , CON $ pval refl $$ A typ $$ A vap $$ Out
>                              $$ A d0 $$ A d1 $$ A (CON q)
>            , x ]
> coerce (EnumT (CONSE _ _,   CONSE _ _))      _  ZE = Right ZE
> coerce (EnumT (CONSE _ e1,  CONSE _ e2))     q  (SU x) = Right . SU $
>   coe @@ [ENUMT e1, ENUMT e2, CON $ q $$ Snd $$ Snd $$ Fst, x]  -- `CONSE` tails
> coerce (EnumT (NILE,        NILE))           q  x = Right x
> coerce (EnumT (NILE,        t@(CONSE _ _)))  q  x = Right $
>   nEOp @@ [q, ENUMT t]
> coerce (EnumT (CONSE _ _,   NILE))           q  x = Right $
>   nEOp @@ [q, ENUMT NILE]
> coerce (Monad (d1, d2) (x1, x2)) q (RETURN v) =
>   Right . RETURN $ coe @@ [x1, x2, CON (q $$ Snd), v]
> coerce (Monad (d1, d2) (x1, x2)) q (COMPOSITE y) =
>   Right . COMPOSITE $ coe @@ [
>       descOp @@ [d1, MONAD d1 x1],
>       descOp @@ [d2, MONAD d2 x2],
>       error "FreeMonad.coerce: missing equality proof",
>       y
>     ]
> -- coerce :: (Can (VAL,VAL)) -> VAL -> VAL -> Either NEU VAL
> coerce (IMu (Just (l0,l1) :?=:
>             (Id (iI0,iI1) :& Id (d0,d1))) (i0,i1)) q (CON x) =
>   let ql  = CON $ q $$ Fst
>       qiI = CON $ q $$ Snd $$ Fst
>       qi  = CON $ q $$ Snd $$ Snd $$ Snd
>       qd = CON $ q $$ Snd $$ Snd $$ Fst
>       typ =
>         PI SET $ L $ "iI" :. [.iI.
>          ARR (ARR (NV iI) (idesc -$ [ NV iI ])) $
>           ARR (NV iI) $
>            ARR (ARR (NV iI) ANCHORS) SET ]
>       vap =
>         L $ "iI" :. [.iI.
>          L $ "d" :. [.d.
>           L $ "i" :. [.i.
>            L $ "l" :. [.l. N $
>             idescOp :@ [ NV iI , N (V d :$ A (NV i))
>                        , L $ "j" :. [.j.
>                           IMU (|(NV l)|) (NV iI) (NV d) (NV j)]
>                        ] ] ] ] ]
>   in Right . CON $
>     coe @@ [ idescOp @@ [  iI0, d0 $$ A i0
>                         ,  L $ "i" :. [.i.
>                             IMU (|(l0 -$ [])|) (iI0 -$ []) (d0 -$ []) (NV i)
>                            ]
>                         ]
>            , idescOp @@ [  iI1, d1 $$ A i1
>                         ,  L $ "i" :. [.i.
>                             IMU (|(l1 -$ [])|) (iI1 -$ []) (d1 -$ []) (NV i)
>                            ]
>                         ]
>            , CON $ pval refl $$ A typ $$ A vap $$ Out
>                              $$ A iI0 $$ A iI1 $$ A qiI
>                              $$ A d0 $$ A d1 $$ A qd
>                              $$ A i0 $$ A i1 $$ A qi
>                              $$ A l0 $$ A l1 $$ A ql
>            , x ]
> coerce (IMu (Nothing :?=: (Id (iI0,iI1) :& Id (d0,d1))) (i0,i1)) q (CON x) =
>   let qiI = CON $ q $$ Fst
>       qi  = CON $ q $$ Snd $$ Snd
>       qd = CON $ q $$ Snd $$ Fst
>       typ =
>         PI SET $ L $ "iI" :. [.iI.
>          ARR (ARR (NV iI) (idesc -$ [ NV iI ])) $
>           ARR (NV iI) SET ]
>       vap =
>         L $ "iI" :. [.iI.
>          L $ "d" :. [.d.
>           L $ "i" :. [.i. N $
>             idescOp :@ [ NV iI , N (V d :$ A (NV i))
>                        , L $ "j" :. [.j.
>                           IMU Nothing (NV iI) (NV d) (NV j)]
>                        ] ] ] ]
>   in Right . CON $
>     coe @@ [ idescOp @@ [ iI0 , d0 $$ A i0
>                         , L $ "i" :. [.i.
>                             IMU Nothing (iI0 -$ []) (d0 -$ []) (NV i) ] ]
>            , idescOp @@ [ iI1 , d1 $$ A i1
>                         , L $ "i" :. [.i.
>                             IMU Nothing (iI1 -$ []) (d1 -$ []) (NV i) ] ]
>            , CON $ pval refl $$ A typ $$ A vap $$ Out
>                              $$ A iI0 $$ A iI1 $$ A qiI
>                              $$ A d0 $$ A d1 $$ A qd
>                              $$ A i0 $$ A i1 $$ A qi
>            , x ]
> coerce (Label (l1, l2) (t1, t2)) q (LRET t) =
>     Right $ LRET $ coe @@ [t1, t2, CON (q $$ Snd), t]
> -- coerce :: (Can (VAL,VAL)) -> VAL -> VAL -> Either NEU VAL
> coerce (Nu (Just (l0,l1) :?=: Id (d0,d1))) q (CON x) =
>   let typ = ARR desc (ARR SET SET)
>       vap = L $ "d" :. [.d. L $ "l" :. [.l. N $
>               descOp :@ [NV d,NU (Just $ NV l) (NV d)] ] ]
>   in Right . CON $
>     coe @@ [ descOp @@ [ d0 , NU (Just l0) d0 ]
>            , descOp @@ [ d1 , NU (Just l1) d1 ]
>            , CON $ pval refl $$ A typ $$ A vap $$ Out
>                              $$ A d0 $$ A d1 $$ A (CON $ q $$ Snd)
>                              $$ A l0 $$ A l1 $$ A (CON $ q $$ Fst)
>            , x ]
> coerce (Nu (Nothing :?=: Id (d0,d1))) q (CON x) =
>   let typ = ARR desc SET
>       vap = L $ "d" :. [.d. N $
>               descOp :@ [NV d,NU Nothing (NV d)] ]
>   in Right . CON $
>     coe @@ [ descOp @@ [ d0 , NU Nothing d0 ]
>            , descOp @@ [ d1 , NU Nothing d1 ]
>            , CON $ pval refl $$ A typ $$ A vap $$ Out
>                              $$ A d0 $$ A d1 $$ A (CON q)
>            , x ]
> coerce Prop              q pP  = Right pP
> coerce (Prf (pP1, pP2))  q p   = Right $ q $$ Fst $$ A p
> coerce (Quotient (_X, _Y) _ _) q (CLASS x) = Right $
>   CLASS (coe @@ [_X, _Y, CON $ q $$ Fst, x])
> coerce (Sigma (sS1, sS2) (tT1, tT2)) q p = Right . PAIR s2 $
>   coe @@ [  tT1 $$ A s1, tT2 $$ A s2
>          ,  CON $ q $$ Snd $$ A s1 $$ A s2 $$ A sq
>          ,  p $$ Snd] where
>     s1 = p $$ Fst
>     (s2, sq) = coeh sS1 sS2 (CON $ q $$ Fst) s1
> coerce Unit q s = Right s
> coerce UId _ u = Right u
> coerce _    q  (N x)  = Left x
> coerce cvv  q  r      = error $ unlines ["coerce: can't cope with sets",
>                             show cvv, "and proof", show q, "and value", show r]

The `partialEq` function takes two sets together with a proof that they
are equal; it returns `True` if they are known to be definitionally
equal. This is sound but not complete for the definitional equality, so
if it returns `False` they might still be equal. It is safe to call
during bquote, and hence during evaluation, because it avoids forcing
the types of references.

> partialEq :: VAL -> VAL -> VAL -> Bool
> partialEq _ _ (N (P r :$ _ :$ _))    | r == refl                = True
> partialEq (C (Mu t1)) (C (Mu t2)) _  | eqLabelIncomplete t1 t2  = True
> partialEq _ _ _ = False

Sadly we cannot do the following, because it is not safe to invent a
name supply.

\< partialEq s t \_ = bquote B0 s ns == bquote B0 t ns \< where ns = (B0
:\< ("\_\_partialEq", 0), 0) :: NameSupply
