<a name="Evidences.Operators">Operators and primitives</a>
========================

> {-# LANGUAGE TypeOperators, GADTs, PatternSynonyms,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts, DataKinds,
>     DeriveDataTypeable #-}

> module Evidences.Operators where

> import Control.Applicative
> import Control.Exception
> import Data.Typeable
> import Kit.BwdFwd
> import Kit.MissingLibrary
> import Evidences.Tm
> import {-# SOURCE #-} Evidences.Eval
> import Evidences.OperatorDSL
> import {-# SOURCE #-} Evidences.DefinitionalEquality
> import {-# SOURCE #-} Evidences.PropositionalEquality
> import NameSupply.NameSupply
> import NameSupply.NameSupplier

In this section, we weave some She aspects. In particular, we bring
inside `Rules.lhs` the `operators` defined by feature files, along with
any auxiliary code.

> operators :: [Op]
> operators = [
>   eqGreen,
>   coe,
>   coh,
>   argsOp,
>   schTypeOp,
>   nEOp,
>   inhEOp,
>   qElimOp,
>   recordOp,
>   splitOp
>   ]

> eqGreen = Op { opName = "eqGreen"
>              , opArity = 4
>              , opTyTel =  "S" :<: SET :-: \ sS -> "s" :<: sS :-: \ s ->
>                           "T" :<: SET :-: \ tT -> "t" :<: tT :-: \ t ->
>                           Target PROP
>              , opRun = opRunEqGreen
>              , opSimp = \_ _ -> empty
>              } where
>              opty chev [y0,t0,y1,t1] = do
>                  (y0 :=>: y0v) <- chev (SET :>: y0)
>                  (t0 :=>: t0v) <- chev (y0v :>: t0)
>                  (y1 :=>: y1v) <- chev (SET :>: y1)
>                  (t1 :=>: t1v) <- chev (y1v :>: t1)
>                  return ([ y0 :=>: y0v
>                          , t0 :=>: t0v
>                          , y1 :=>: y1v
>                          , t1 :=>: t1v ]
>                         , PROP)
>              opty _  _             = throwErrMsg "eqGreen: invalid arguments."

> coe = Op { opName = "coe" -- "coerce" -- transport values between equal types
>          , opArity = 4
>          , opTyTel =  "S" :<: SET :-: \ sS -> "T" :<: SET :-: \ tT ->
>                       "Q" :<: PRF (EQBLUE (SET :>: sS) (SET :>: tT)) :-: \ _ ->
>                       "s" :<: sS :-: \ _ -> Target tT
>          , opRun = oprun
>          , opSimp = \ [sS, tT, _, s] r -> case s of
>              N s | equal (SET :>: (sS, tT)) r -> pure s
>              _ -> empty
>          } where
>          oprun :: [VAL] -> Either NEU VAL
>          oprun [_S, _T, q, v] | partialEq _S _T q = Right v
>          -- oprun [C (Mu t0), C (Mu t1), q, s] = case halfZip (Mu (dropLabel t0)) (Mu (dropLabel t1)) of
>          --   Nothing -> Right $ nEOp @@ [q $$ Out, C (Mu t1)]
>          --   Just fxy -> coerce fxy (q $$ Out) s
>          oprun [C x,C y,q,s] = case halfZip x y of
>            Nothing  -> Right $ nEOp @@ [q $$ Out, C y]
>            Just fxy -> coerce fxy (q $$ Out) s
>          oprun [N x,y,q,s] = Left x
>          oprun [x,N y,q,s] = Left y
>          oprun vs = error ("coe: undefined for arguments"
>                                ++ unlines (map show vs))

> coh = Op { opName = "coh" -- "coherence"
>          , opArity = 4
>          , opTyTel =
>              "S" :<: SET :-: \ _S -> "T" :<: SET :-: \ _T ->
>              "Q" :<: PRF (EQBLUE (SET :>: _S) (SET :>: _T)) :-: \ _Q ->
>              "s" :<: _S :-: \ s -> Target $ PRF $
>              EQBLUE (_S :>: s) (_T :>: (coe @@ [_S, _T, _Q, s]))
>          , opRun = oprun
>          , opSimp = \ [_S, _T, _, s] r ->
>              if equal (SET :>: (_S, _T)) r
>                then pure $ P refl :$ A _S :$ A s
>                else empty
>          } where
>          oprun :: [VAL] -> Either NEU VAL
>          oprun [_S, _T, q, s] | partialEq _S _T q =
>            Right (pval refl $$ A _S $$ A s)
>          oprun [N x,y,q,s] = Left x
>          oprun [x,N y,q,s] = Left y
>          oprun [_S,_T,_Q,s] = Right $
>            pval cohAx $$ A _S $$ A _T $$ A _Q $$ A s
>          oprun vs = error ("coe: undefined for arguments"
>                                ++ unlines (map show vs))

> argsOp = Op
>   {  opName = "args"
>   ,  opArity = 1
>   ,  opTyTel = "s" :<: SCH :-: \ _ -> Target SET
>   ,  opRun = \ [s] -> argsOpRun s
>   ,  opSimp = \ _ _ -> empty
>   }

> schTypeOp = Op
>   {  opName = "schType"
>   ,  opArity = 1
>   ,  opTyTel = "s" :<: SCH :-: \ _ -> Target SET
>   ,  opRun = \ [s] -> schTypeOpRun s
>   ,  opSimp = \ _ _ -> empty
>   }

> argsOpRun :: VAL -> Either NEU VAL
> argsOpRun (SCHTY _)       = Right UNIT
> argsOpRun (SCHEXPPI s t)  =
>   Right $ SIGMA (schTypeOp @@ [s])
>            (L ("x" :. (let x = 0 :: Int in N $ argsOp :@ [t -$ [ NV x ]])))
> argsOpRun (SCHIMPPI s t)  =
>   Right $ SIGMA s
>            (L ("x" :. (let x = 0 :: Int in N $ argsOp :@ [t -$ [ NV x ]])))
> argsOpRun (N v)           = Left v


> schTypeOpRun :: VAL -> Either NEU VAL
> schTypeOpRun (SCHTY s)       = Right s
> schTypeOpRun (SCHEXPPI s t)  =
>   Right $ PI (schTypeOp @@ [s])
>            (L ("x" :. (let x = 0 :: Int in N $ schTypeOp :@ [t -$ [ NV x ]])))
> schTypeOpRun (SCHIMPPI s t)  =
>   Right $ PI s
>            (L ("x" :. (let x = 0 :: Int in N $ schTypeOp :@ [t -$ [ NV x ]])))
> schTypeOpRun (N v)           = Left v

> nEOp = Op { opName = "naughtE"
>           , opArity = 2
>           , opTyTel =  "z" :<: PRF ABSURD :-: \ _ ->
>                        "X" :<: SET :-: \ xX -> Target xX
>           , opRun = runOpTree $ OCon $ OBarf
>           , opSimp = \_ _ -> empty
>           }

> inhEOp = Op { opName = "inh"
>             , opArity = 4
>             , opTyTel = "S" :<: SET :-: \ ty ->
>                         "p" :<: PRF (INH ty) :-: \ p ->
>                         "P" :<: IMP (PRF (INH ty)) PROP :-: \ pred ->
>                         "m" :<: PI ty (L $ "s" :. (let t = 0 :: Int in
>                                          pred -$ [ WIT (NV t) ] )) :-: \ _ ->
>                         Target (PRF (pred $$ A p))
>             , opRun = \[_,p,_,m] -> case p of
>                                       WIT t -> Right $ m $$ A t
>                                       N n   -> Left n
>             , opSimp = \_ _ -> empty
>             }

> qElimOp = Op
>   { opName  = "elimQuotient"
>   , opArity = 7
>   , opTyTel = "X" :<: SET                             :-: \_X ->
>               "R" :<: ARR _X (ARR _X PROP)            :-: \_R ->
>               "p" :<: PRF (equivalenceRelation _X _R) :-: \p ->
>               "z" :<: QUOTIENT _X _R p                :-: \z ->
>               "P" :<: ARR (QUOTIENT _X _R p) SET      :-: \_P ->
>               "m" :<: (PI _X $ L $ "x" :. (let x = 0 :: Int in _P -$ [ CLASS (NV x) ] ))
>                                                       :-: \m ->
>               "h" :<: PRF (ALL _X $ L $ "x" :. (let x = 0 :: Int in
>                             ALL (_X -$ []) $ L $ "y" :. (let y = 0; x = 1 in
>                              IMP (_R -$ [ NV x , NV y ])
>                               (EQBLUE (_P -$ [ CLASS (NV x) ]
>                                           :>: m -$ [ NV x ])
>                                       (_P -$ [ CLASS (NV y) ]
>                                           :>: m -$ [ NV y ])) ) ))
>                                                       :-: \_ ->
>               Target $ _P $$ A z
>   , opRun = run
>   , opSimp = \_ _ -> empty
>   } where
>     run :: [VAL] -> Either NEU VAL
>     run [_, _, _, CLASS x, _, m, _] = Right (m $$ A x)
>     run [_, _, _, N n, _, _, _]     = Left n

> recordOp = Op
>   { opName   = "Record"
>   , opArity  = 1
>   , opTyTel  = recordOpTy
>   , opRun    = recordOpRun
>   , opSimp   = \_ _ -> empty
>   } where
>       recordOpTy = "sig" :<: RSIG :-: \sig ->
>                    Target SET
>       recordOpRun :: [VAL] -> Either NEU VAL
>       recordOpRun [REMPTY]           = Right UNIT
>       recordOpRun [RCONS sig id ty]  = Right $ SIGMA (recordOp @@ [sig]) ty
>       recordOpRun [N x]              = Left x

> splitOp = Op
>   { opName = "split" , opArity = 5
>   , opTyTel =  "A"   :<: SET                          :-: \ aA ->
>                "B"   :<: ARR aA SET                   :-: \ bB ->
>                "ab"  :<: SIGMA aA bB                  :-: \ ab ->
>                "P"   :<: ARR (SIGMA aA bB) SET        :-: \ pP ->
>                "p"   :<: (
>                  PI aA $ L $ "a" :. (let a = 0 :: Int in
>                   PI (bB -$ [ NV a ]) $ L $ "b" :. (let b = 0; a = 1 in
>                    pP -$ [ PAIR (NV a) (NV b) ] ) ))  :-: \ p ->
>                Target $ pP $$ A ab
>   , opRun = runOpTree $
>       oLams $ \ () () ab () p -> ORet $ p $$ A (ab $$ Fst) $$ A (ab $$ Snd)
>   , opSimp = \_ _ -> empty
>   }

> cohAx = [("Axiom",0),("coh",0)] := (DECL :<: cohType) where
>   cohType = PRF $
>             ALL SET $ L $ "S" :. (let _S = 0 :: Int in
>             ALL SET $ L $ "T" :. (let _T = 0; _S = 1 in
>             ALL (PRF (EQBLUE (SET :>: NV _S) (SET :>: NV _T)))
>                $ L $ "Q" :. (let _Q = 0; _T = 1; _S = 2 in
>             ALL (NV _S) $ L $ "s" :. (let s = 0; _Q = 1; _T = 2; _S = 3 in
>             EQBLUE (NV _S :>: NV s)
>                    (NV _T :>: N (coe :@ [NV _S, NV _T, NV _Q, NV s]))
>             ))))

> refl = [("Axiom",0),("refl",0)] := (DECL :<: reflType) where
>   reflType = PRF $  ALL SET $ L $ "S" :. (let _S = 0 :: Int in
>                     ALL (NV _S) $ L $ "s" :. (let s = 0; _S = 1 in
>                     EQBLUE (NV _S :>: NV s) (NV _S :>: NV s) ))

> substEq = [("Primitive", 0), ("substEq", 0)] := DEFN seDef :<: seTy where
>   seTy = PI SET $ L $ "X" :. (let _X = 0 :: Int in
>              PI (NV _X) $ L $ "x" :. (let x = 0; _X = 1 in
>              PI (NV _X) $ L $ "y" :. (let y = 0; x = 1; _X = 2 in
>              PI (PRF (EQBLUE (NV _X :>: NV x) (NV _X :>: NV y))) $ L $ "q" :. (let q = 0; y = 1; x = 2; _X = 3 in
>              PI (ARR (NV _X) SET) $ L $ "P" :. (let _P = 0; q = 1; y = 2; x = 3; _X = 4 in
>              ARR (N (V _P :$ A (NV x))) (N (V _P :$ A (NV y)))
>              )))))
>   seDef = L $ "X" :. (let _X = 0 :: Int in
>             L $ "x" :. (let x = 0; _X = 1 in
>             L $ "y" :. (let y = 0; x = 1; _X = 2 in
>             L $ "q" :. (let q = 0; y = 1; x = 2; _X = 3 in
>             L $ "P" :. (let _P = 0; q = 1; y = 2; x = 3; _X = 4 in
>             L $ "px" :. (let px = 0; _P = 1; q = 2; y = 3; x = 4; _X = 5 in
>             N (coe :@ [N (V _P :$ A (NV x)), N (V _P :$ A (NV y)),
>                 CON (N (P refl :$ A (ARR (NV _X) SET) :$ A (NV _P) :$ Out
>                           :$ A (NV x) :$ A (NV y) :$ A (NV q))),
>                 NV px])
>             ))))))

> symEq = [("Primitive", 0), ("symEq", 0)] := DEFN def :<: ty where
>   ty = PRF $ ALL SET $ L $ "X" :. (let _X = 0 :: Int in
>                  ALL (NV _X) $ L $ "x" :. (let x = 0; _X = 1 in
>                  ALL (NV _X) $ L $ "y" :. (let y = 0; x = 1; _X = 2 in
>                  IMP (EQBLUE (NV _X :>: NV x) (NV _X :>: NV y))
>                  (EQBLUE (NV _X :>: NV y) (NV _X :>: NV x))
>              )))
>   def = L $ "X" :. (let _X = 0 :: Int in
>         L $ "x" :. (let x = 0; _X = 1 in
>         L $ "y" :. (let y = 0; x = 1; _X = 2 in
>         L $ "q" :. (let q = 0; y = 1; x = 2; _X = 3 in
>         N (P refl :$ A (ARR (NV _X) SET)
>             :$ A (L $ "z" :. (let z = 0; q = 1; y = 2; x = 3; _X = 4 in
>                 PRF (EQBLUE (NV _X :>: NV z) (NV _X :>: NV x))))
>             :$ Out
>             :$ A (NV x)
>             :$ A (NV y)
>             :$ A (NV q)
>             :$ Fst
>             :$ A (N (P refl :$ A (NV _X) :$ A (NV x))))
>         ))))

> equivalenceRelation :: VAL -> VAL -> VAL
> equivalenceRelation a r =
>   -- refl
>   AND (ALL a $ L $ "x" :. (let x = 0 :: Int in x =~ x )) $
>   -- sym
>   AND (ALL a $ L $ "x" :. (let x = 0 :: Int in
>         ALL (a -$ []) $ L $ "y" :. (let y = 0; x = 1 in
>          IMP (x =~ y) (y =~ x) ))
>       ) $
>   -- trans
>       (ALL a $ L $ "x" :. (let x = 0 :: Int in
>         ALL (a -$ []) $ L $ "y" :. (let y = 0; x = 1 in
>          ALL (a -$ []) $ L $ "z" :. (let z = 0; y = 1; x = 2 in
>           IMP (x =~ y) (IMP (y =~ z) (x =~ z)))))
>       )
>   where
>     x =~ y = r -$ [ NV x , NV y ]

The list of `primitives` includes axioms and fundamental definitions
provided by the `Primitives` aspect, plus a reference corresponding to
each operator.

> primitives :: [(String, REF)]
> primitives = map (\op -> (opName op, mkRef op)) operators ++ [
>     ("cohAx", cohAx),
>     ("refl", refl),
>     ("substEq", substEq),
>     ("symEq", symEq)
>     ]
>   where
>     mkRef :: Op -> REF
>     mkRef op = [("Operators",0),(opName op,0)] := (DEFN opEta :<: opTy)
>       where
>         nameSupply :: NameSupply
>         nameSupply = (bwdList [("Operators",0), (opName op,0), ("opTy",0)], 0)
>         opTy = pity (opTyTel op) nameSupply
>         ari = opArity op
>         args = map NV [(ari-1),(ari-2)..0]
>         names = take (ari-1) (map (\x -> [x]) ['b'..])
>         opEta = L $ "a" :. Prelude.foldr (\s x -> L (s :. x)) (N $ op :@ args) names

We can look up the primitive reference corresponding to an operator
using `lookupOpRef`. This ensures we maintain sharing of these
references.

> lookupOpRef :: Op -> REF
> lookupOpRef op = case lookup (opName op) primitives of
>     Just ref  -> ref
>     Nothing   -> error $ "lookupOpRef: missing operator primitive " ++ show op

> -- "type undefined
> data PiTyException = PiTyException String TY deriving (Show, Typeable)
> instance Exception PiTyException

As in "Pi Type", not "Pity the fool"

> pity :: NameSupplier m => TEL TY -> m TY
> pity (Target t)       = return t
> pity (x :<: s :-: t)  = do
>   let badPiTy = throw (PiTyException x s)
>   freshRef  (x :<: badPiTy)
>             (\xref -> do
>                t' <- pity $ t (pval xref)
>                -- XXX type isn't SET
>                t'' <- mQuote (SET :>: t')
>                return $ PI s (L $ x :. t''))
