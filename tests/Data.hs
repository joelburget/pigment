module Data where

import Control.Monad

import Test.Tasty
import Test.Tasty.HUnit

import Cochon.Model
import Evidences.Tm
import ProofState.Edition.ProofContext
import Tactics.Data

import ProofState.Edition.Navigation
import Control.Applicative
import Cochon.PrettyProofState
import DisplayLang.Name
import DisplayLang.DisplayTm
import ProofState.Edition.GetSet
import ProofState.Interface.Name
import ProofState.Interface.NameResolution
import ProofState.Interface.Search
import ProofState.Edition.ProofState


import Elaboration.Error
import DisplayLang.PrettyPrint


runScript :: ProofState a -> (a -> IO ()) -> IO ()
runScript script continue = case runProofState script emptyContext of
    Left e -> assertFailure (renderHouseStyle (prettyStackError e))
    Right (a, _) -> continue a


assertThrows :: String -> ProofState a -> IO ()
assertThrows msg script = case runProofState script emptyContext of
    Left _ -> return ()
    Right _ -> assertFailure msg


emptyDataTest :: Assertion
emptyDataTest =
    let script = do
            dataName <- emptyData "foo"
            Just (_ :=>: val) <- lookupName dataName
            return (dataName, val)

        continue (name, val) = do
            assertEqual "" [("foo", 1)] name
            assertEqual ""
                (MU (Just (ANCHOR (TAG "foo") SET ALLOWEDEPSILON)) IDD)
                val

    in runScript script continue


addConstructorTest :: String -> ProofState a -> Assertion
addConstructorTest


tests :: TestTree
tests = testGroup "data"
    [ testCase "empty data" emptyDataTest
    , testCase "add constructor" $
        addConstructorTest "unit data type" $ do
            data <- emptyData "unit"
            addConstructor "unit"
    ]
