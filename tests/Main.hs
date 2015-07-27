{-# LANGUAGE TypeOperators #-}

module Main where

import Data.Either

import Test.Tasty
import Test.Tasty.HUnit

import PigmentPrelude

import qualified TacticParse as Parse
import qualified Operators
import qualified AlphaConversions
import qualified Mangler
import qualified Records
import qualified OTT

canTyBasics :: Assertion
canTyBasics = do
    -- let's start with the basics
    assertRight "Set"
        Set
        (canTy ev (Set :>: Set))

    -- -- Can ((TY :>: VAL) :=>: VAL)
    -- let s = (SET :>: SET) :=>: SET
    -- assertRight "Pi"
    --     (Pi s s)
    --     -- (do
    --     --     s' <- ev (SET :>: s)
    --     --     return (Pi (SET :>: s) ((ARR s' SET) :>: t))
    --     -- )
    --     (canTy ev (Set :>: Pi s s))

-- check :: (TY :>: INTM) -> Check INTM (INTM :=>: VAL)
checkBasics :: Assertion
checkBasics = do
    -- some trivial checks
    assertChecks (SET :>: SET) SET
    assertChecks (SET :>: PROP) PROP
    assertChecks (SET :>: PROB) PROB
    assertChecks (SET :>: RSIG) RSIG
    assertChecks (RSIG :>: REMPTY) REMPTY
    assertChecks (UNIT :>: VOID) VOID
    assertChecks (SET :>: UID) UID

    -- assertChecks (PI SET (L (K SET)) :>: L ("s" :. SET)) (L (K SET))
    assertChecks (PI SET (L (K SET)) :>: L (K SET)) (L (K SET))

-- infer :: EXTM -> Check INTM (VAL :<: TY)
inferBasics :: Assertion
inferBasics = do
    -- trivial checks - we infer the ascripted type
    assertInfers (UNIT ?? SET) (UNIT :<: SET)
    assertInfers (VOID ?? UNIT) (VOID :<: UNIT)

    assertInfers (ARR UNIT UNIT ?? SET)
                 (ARR UNIT UNIT :<: SET)
    assertInfers (LK VOID ?? ARR UNIT UNIT)
                 (LK VOID :<: ARR UNIT UNIT)

    -- this SIGMA and TIMES are really the same thing
    assertInfers (PAIR UNIT UNIT ??  SIGMA SET (LK SET))
                 (PAIR UNIT UNIT :<: TIMES SET SET)

    -- this ARR and PI are really the same thing
    assertInfers (LAV "x" (NV 0) ?? ARR SET SET)
                 (LAV "x" (NV 0) :<: PI SET (LK SET))

    -- elimination
    -- assertInfers
    --     ((constUnit :? constUnitTy) :$ (A UNIT))
    --     (UNIT :<: SET)

equalBasics :: Assertion
equalBasics = do
    let pair = PAIR UNIT UNIT
        result = pair $$ Fst
    assertTrue $ equal (SET :>: (result, UNIT)) fakeNameSupply

checkTests :: TestTree
checkTests = testGroup "Type Checking Tests"
    [ testCase "canTy basics" canTyBasics
    , testCase "check basics" checkBasics
    , testCase "infer basics" inferBasics
    , testCase "equal basics" equalBasics
    -- , testCase "tactics" testTactics
    ]

tests :: TestTree
tests = testGroup "Tests"
    [ checkTests
    , Parse.tests
    , Operators.tests
    , AlphaConversion.tests
    , Mangler.tests
    , Records.tests
    , OTT.tests
    ]

main :: IO ()
main = defaultMain tests
