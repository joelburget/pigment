{-# LANGUAGE TypeOperators #-}

module Main where

import Data.Either

import Test.Tasty
import Test.Tasty.HUnit

import Evidences.TypeChecker
import Evidences.Tm
import Kit.BwdFwd
import NameSupply.NameSupplier
import NameSupply.NameSupply


ev :: (TY :>: VAL) -> Either (StackError VAL) ((TY :>: VAL) :=>: VAL)
ev tx@(_ :>: x) = Right (tx :=>: x)

assertRight :: (Eq a, Show a, Show b) => String -> a -> Either b a -> Assertion
assertRight msg _ (Left err) = assertFailure (msg ++ " " ++ show err)
assertRight msg a (Right a') = assertEqual msg a a'

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

fakeNameSupply :: NameSupply
fakeNameSupply = (B0, 0)

assertChecks :: (TY :>: INTM) -> VAL -> Assertion
assertChecks start finish =
    let resultVal = do
            _ :=>: val <- typeCheck (check start) fakeNameSupply
            return val
    in assertRight "checks" finish resultVal

assertNoCheck :: (TY :>: INTM) -> Assertion
assertNoCheck problem =
    let result = typeCheck (check problem) fakeNameSupply
    in assertBool "doesn't check" (isLeft result)

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

assertInfers :: EXTM -> (VAL :<: TY) -> Assertion
assertInfers start finish =
    let resultVal = typeCheck (infer start) fakeNameSupply
    in assertRight "infers" finish resultVal

-- infer :: EXTM -> Check INTM (VAL :<: TY)
inferBasics :: Assertion
inferBasics = do
    -- trivial checks - we infer the ascripted type
    assertInfers (UNIT :? SET) (UNIT :<: SET)

    let constUnit = LK UNIT
        constUnitTy = PI SET (LK UNIT)
    assertInfers (constUnit :? constUnitTy) (constUnit :<: constUnitTy)

    -- elimination
    -- assertInfers
    --     ((constUnit :? constUnitTy) :$ (A UNIT))
    --     (UNIT :<: SET)

tests :: TestTree
tests = testGroup "Tests"
    [ testCase "canTy basics" canTyBasics
    , testCase "check basics" checkBasics
    , testCase "infer basics" inferBasics
    ]

main :: IO ()
main = defaultMain tests
