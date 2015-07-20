module Mangler (tests) where

import Test.Tasty
import Test.Tasty.HUnit

import Evidences.Mangler
import Evidences.Tm
import Kit.BwdFwd

testUnderScope :: Assertion
testUnderScope = do
    let x = [("x", 0)]
        npX = NP x
        y = [("y", 0)]
        npY = NP y

    -- constant, it doesn't matter what we try to instantiate it to
    assertEqual "" npX (underScope (K npX) y)
    assertEqual "" npX (underScope (K npX) x)

    assertEqual "" UID (underScope ("z" :. UID) x)
    assertEqual "" (PAIR npX npX) (underScope ("z" :. (PAIR (NV 0) (NV 0))) x)
    assertEqual ""
        (PAIR npX (NV 1))
        (underScope ("z" :. (PAIR (NV 0) (NV 1))) x)

    let idVal = NP ([("idVal", 0)] := DEFN IDD :<: MU Nothing IDN)
        constVal = NP ([("constVal", 0)] := DEFN (CONSTD UNIT) :<: MU Nothing CONSTN)
        env = (B0 :< IDN :< CONSTN, [])

    assertEqual "" UID (underScope (H env "x" UID) (NV 0))
    assertEqual "" UID (underScope (H env "x" UID) (NV 1))
    assertEqual "" UID (underScope (H env "x" UID) (NV 2))

-- testUnder :: Assertion
-- testUnder = do
--     let mangle = under
--     assertEqual

tests :: TestTree
tests = testGroup "mangler"
  [ testCase "underScope" testUnderScope
  -- , testCase "under" testUnder
  -- , testCase "-||"
  -- , testCase "substitute"
  -- , testCase "inc"
  ]
