{-# LANGUAGE TypeOperators, OverloadedStrings #-}

module Operators (tests) where

import Control.Applicative
import Control.Exception

import Test.Tasty
import Test.Tasty.HUnit

import Distillation.ShowPity
import Evidences.Operators
import Evidences.Tm
import Evidences.TypeChecker
import Kit.BwdFwd
import NameSupply.NameSupplier
import NameSupply.NameSupply


inCheck :: Check INTM (INTM :=>: VAL) -> NameSupply -> Assertion
inCheck check supply = case typeCheck check supply of
    Left err -> assertFailure $ "did not check:\n" ++ show err
    Right _ -> return ()

testLookupOpRef :: Op -> Assertion
testLookupOpRef op =
    let ref = lookupOpRef op
        m = check (pty ref :>: NP ref)
    in inCheck m (B0 :< ("tactics", 0), 0)

-- testPrimitive :: REF -> Assertion
-- testPrimitive ref =
--     let m = do opTy' <- pity (opTyTel)
--     inCheck

tests :: TestTree
tests =
  let catchPity :: PiTyException -> IO ()
      catchPity = assertFailure . showPity
      testOp op = testCase (opName op) (testLookupOpRef op `catch` catchPity)
  in testGroup "operators" (map testOp operators)
  -- (map (\op -> testCase (opName op) (testLookupOpRef op)) [qElimOp, splitOp])
  -- (map (\(name, ref) -> testCase name (testLookupOpRef ref)) primitives)
