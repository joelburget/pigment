{-# LANGUAGE PatternSynonyms #-}
module Ornament where

import Test.Tasty
import Test.Tasty.HUnit

import Evidences.Tm
import Evidences.Ornament


type TYDESC = TyDesc INTM
type CONDESC = ConDesc INTM

-- pattern RET i = C (Ornament (Ret i))
-- pattern ARG a f = C (Ornament (Arg a f))
-- pattern REC i d = C (Ornament (Rec i d))

unitDesc :: TYDESC
unitDesc = TyDesc
    []
    ["Unit" :<: ConRet ()]


pairDesc :: TYDESC
pairDesc = TyDesc
    [("x" :<: SET), ("y" :<: SET)]
    -- XXX how does binding work?
    ["pair" :<: (ConArg ("fst" :<: (NV 1)) (ConArg ("snd" :<: (NV 0)) (ConRet ())))]


natDesc :: TYDESC
natDesc = TyDesc
    []
    [ "z" :<: ConRet ()
    , "suc" :<: (ConRec ("n" :<: ()) (ConRet ()))
    ]


tests :: TestTree
tests = testGroup "Ornament"

    [ testGroup "nat"
        [
        ]
    ]
