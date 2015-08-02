{-# LANGUAGE TypeOperators #-}

module PigmentPrelude
    ( ev
    , fakeNameSupply
    , assertRight
    , assertChecks
    , assertNoCheck
    , module X
    ) where

import Data.Either

import Test.Tasty
import Test.Tasty.HUnit

import Evidences.DefinitionalEquality as X
import Evidences.Eval                 as X
import Evidences.Operators            as X
import Evidences.TypeChecker          as X
import Evidences.Tm                   as X
import Kit.BwdFwd                     as X
import NameSupply.NameSupplier        as X
import NameSupply.NameSupply          as X


assertThrows :: String -> ProofState a -> IO ()
assertThrows msg script = case runProofState script emptyContext of
    Left _ -> return ()
    Right _ -> assertFailure msg


runScript :: ProofState a -> (a -> IO ()) -> IO ()
runScript script continue = case runProofState script emptyContext of
    Left e -> assertFailure (renderHouseStyle (prettyStackError e))
    Right (a, _) -> continue a


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

easiestest =
    let bool = SUMD UNIT UNIT ?? SET
    in typeCheck (infer bool) (B0, 0)

easiest =
    let arr = LAV "A" (SUMD (NV 0) UNIT)
        arrTy = ARR SET SET
        bool = (arr ?? arrTy) $## [UNIT]
    in typeCheck (infer bool) (B0, 1)

easier =
        -- (A, B)
    -- let pairer = PIV "A" SET
    --             (PIV "B" SET
    --                 (SUMD (NV 1) (NV 0)))

    let pairer = LAV "A" (LAV "B" (SUMD (NV 1) (NV 0)))
        pairerTy = ARR SET (ARR SET SET)

    -- let a = N (P ([("A", 0)] := DECL :<: SET))
    --     b = N (P ([("B", 0)] := DECL :<: SET))
    --     pairer = SUMD a b
        bool = (pairer ?? pairerTy) $## [UNIT, UNIT]
    in typeCheck (infer bool) (B0, 2)
    -- in equal (SET :>: (N bool, SUMD UNIT UNIT)) fakeNameSupply

-- eliminated =
--     let bool = SUMD UNIT UNIT
--         -- \Either () () -> a or b
--         chooser = LAV "b" (
--         result = pair $$ Fst
--     in equal (SET :>: (result, UNIT)) fakeNameSupply

-- ex :: Either (StackError INTM) (VAL :<: TY)
-- ex = typeCheck (check (PIV "bool" (PAIR UNIT UNIT) (

-- ex = typeCheck (infer (LAV "x" (NV 0) ?? PI SET (LK SET))) fakeNameSupply
