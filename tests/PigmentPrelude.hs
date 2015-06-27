{-# LANGUAGE TypeOperators #-}

module PigmentPrelude
    ( ev
    , fakeNameSupply
    , assertRight
    , assertChecks
    , assertNoCheck
    ) where

import Data.Either

import Test.Tasty
import Test.Tasty.HUnit

import Evidences.TypeChecker   as X
import Evidences.Tm            as X
import Kit.BwdFwd              as X
import NameSupply.NameSupplier as X
import NameSupply.NameSupply   as X


ev :: (TY :>: VAL) -> Either (StackError VAL) ((TY :>: VAL) :=>: VAL)
ev tx@(_ :>: x) = Right (tx :=>: x)

fakeNameSupply :: NameSupply
fakeNameSupply = (B0, 0)

assertRight :: (Eq a, Show a, Show b) => String -> a -> Either b a -> Assertion
assertRight msg _ (Left err) = assertFailure (msg ++ " " ++ show err)
assertRight msg a (Right a') = assertEqual msg a a'

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

assertInfers :: EXTM -> (VAL :<: TY) -> Assertion
assertInfers start finish =
    let resultVal = typeCheck (infer start) fakeNameSupply
    in assertRight "infers" finish resultVal

ex :: Either (StackError INTM) (VAL :<: TY)
ex = typeCheck (infer (LAV "x" (NV 0) ?? PI SET (LK SET))) fakeNameSupply
