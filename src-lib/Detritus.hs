
coerce (Mu (Just (l0,l1) :?=: Identity (d0,d1))) q (CON x) =
  let typ = ARR desc (ARR ANCHORS SET)
      vap = L $ "d" :. (let d = 0 :: Int in L $ "l" :. (let {l = 0; d = 1} in N $
              descOp :@ [NV d,MU (Just $ NV l) (NV d)] ) )
  in Right . CON $
    coe @@ [ descOp @@ [ d0 , MU (Just l0) d0 ]
           , descOp @@ [ d1 , MU (Just l1) d1 ]
           , CON $ pval refl $$ A typ $$ A vap $$ Out
                             $$ A d0 $$ A d1 $$ A (CON $ q $$ Snd)
                             $$ A l0 $$ A l1 $$ A (CON $ q $$ Fst)
           , x ]
coerce (Mu (Nothing :?=: Identity (d0,d1))) q (CON x) =
  let typ = ARR desc SET
      vap = L $ "d" :. (let d = 0 :: Int in N $
              descOp :@ [NV d,MU Nothing (NV d)] )
  in Right . CON $
    coe @@ [ descOp @@ [ d0 , MU Nothing d0 ]
           , descOp @@ [ d1 , MU Nothing d1 ]
           , CON $ pval refl $$ A typ $$ A vap $$ Out
                             $$ A d0 $$ A d1 $$ A (CON q)
           , x ]
coerce (EnumT (CONSE _ _,   CONSE _ _))      _  ZE = Right ZE
coerce (EnumT (CONSE _ e1,  CONSE _ e2))     q  (SU x) = Right . SU $
  coe @@ [ENUMT e1, ENUMT e2, CON $ q $$ Snd $$ Snd $$ Fst, x]  -- `CONSE` tails
coerce (EnumT (NILE,        NILE))           q  x = Right x
coerce (EnumT (NILE,        t@(CONSE _ _)))  q  x = Right $
  nEOp @@ [q, ENUMT t]
coerce (EnumT (CONSE _ _,   NILE))           q  x = Right $
  nEOp @@ [q, ENUMT NILE]
coerce (Monad (d1, d2) (x1, x2)) q (RETURN v) =
  Right . RETURN $ coe @@ [x1, x2, CON (q $$ Snd), v]
coerce (Monad (d1, d2) (x1, x2)) q (COMPOSITE y) =
  Right . COMPOSITE $ coe @@ [
      descOp @@ [d1, MONAD d1 x1],
      descOp @@ [d2, MONAD d2 x2],
      error "FreeMonad.coerce: missing equality proof",
      y
    ]
-- coerce :: (Can (VAL,VAL)) -> VAL -> VAL -> Either NEU VAL
coerce (IMu (Just (l0,l1) :?=:
            (Identity (iI0,iI1) :& Identity (d0,d1))) (i0,i1)) q (CON x) =
  let ql  = CON $ q $$ Fst
      qiI = CON $ q $$ Snd $$ Fst
      qi  = CON $ q $$ Snd $$ Snd $$ Snd
      qd = CON $ q $$ Snd $$ Snd $$ Fst
      typ =
        PI SET $ L $ "iI" :. (let { iI = 0 } in
         ARR (ARR (NV iI) (idesc -$ [ NV iI ])) $
          ARR (NV iI) $
           ARR (ARR (NV iI) ANCHORS) SET )
      vap =
        L $ "iI" :. (let { iI = 0 :: Int } in
         L $ "d" :. (let { d = 0; iI = 1 } in
          L $ "i" :. (let { i = 0; d = 1; iI = 2} in
           L $ "l" :. (let { l = 0; i = 1; d = 2; iI = 3 } in N $
            idescOp :@ [ NV iI , N (V d :$ A (NV i))
                       , L $ "j" :. (let { j = 0; l = 1; i = 2; d = 3; iI = 4 } in
                          IMU (pure (NV l)) (NV iI) (NV d) (NV j))
                       ] ) ) ) )
  in Right . CON $
    coe @@ [ idescOp @@ [  iI0, d0 $$ A i0
                        ,  L $ "i" :. (let { i = 0 :: Int } in
                            IMU (pure (l0 -$ [])) (iI0 -$ []) (d0 -$ []) (NV i)
                           )
                        ]
           , idescOp @@ [  iI1, d1 $$ A i1
                        ,  L $ "i" :. (let { i = 0 :: Int } in
                            IMU (pure (l1 -$ [])) (iI1 -$ []) (d1 -$ []) (NV i)
                           )
                        ]
           , CON $ pval refl $$ A typ $$ A vap $$ Out
                             $$ A iI0 $$ A iI1 $$ A qiI
                             $$ A d0 $$ A d1 $$ A qd
                             $$ A i0 $$ A i1 $$ A qi
                             $$ A l0 $$ A l1 $$ A ql
           , x ]
coerce (IMu (Nothing :?=: (Identity (iI0,iI1) :& Identity (d0,d1))) (i0,i1)) q (CON x) =
  let qiI = CON $ q $$ Fst
      qi  = CON $ q $$ Snd $$ Snd
      qd = CON $ q $$ Snd $$ Fst
      typ =
        PI SET $ L $ "iI" :. (let { iI = 0 :: Int } in
         ARR (ARR (NV iI) (idesc -$ [ NV iI ])) $
          ARR (NV iI) SET )
      vap =
        L $ "iI" :. (let { iI = 0 :: Int } in
         L $ "d" :. (let { d = 0; iI = 1 } in
          L $ "i" :. (let { i = 0; d = 1; iI = 2 } in N $
            idescOp :@ [ NV iI , N (V d :$ A (NV i))
                       , L $ "j" :. (let { j = 0; i = 1; d = 2; iI = 3 } in
                          IMU Nothing (NV iI) (NV d) (NV j))
                       ] ) ) )
  in Right . CON $
    coe @@ [ idescOp @@ [ iI0 , d0 $$ A i0
                        , L $ "i" :. (let { i = 0 :: Int } in
                            IMU Nothing (iI0 -$ []) (d0 -$ []) (NV i) ) ]
           , idescOp @@ [ iI1 , d1 $$ A i1
                        , L $ "i" :. (let { i = 0 :: Int } in
                            IMU Nothing (iI1 -$ []) (d1 -$ []) (NV i) ) ]
           , CON $ pval refl $$ A typ $$ A vap $$ Out
                             $$ A iI0 $$ A iI1 $$ A qiI
                             $$ A d0 $$ A d1 $$ A qd
                             $$ A i0 $$ A i1 $$ A qi
           , X ]
