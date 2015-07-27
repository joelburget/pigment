module Records where

import Control.Monad

import Test.Tasty
import Test.Tasty.HUnit

import Cochon.Model
import Evidences.Tm
import ProofState.Edition.ProofContext
import Tactics.Record

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
import Kit.Trace


runScript :: ProofState a -> (a -> IO ()) -> IO ()
runScript script continue = case runProofState script emptyContext of
    Left e -> assertFailure (renderHouseStyle (prettyStackError e))
    Right (a, _) -> continue a


assertThrows :: String -> ProofState a -> IO ()
assertThrows msg script = case runProofState script emptyContext of
    Left _ -> return ()
    Right _ -> assertFailure msg


emptyRecord :: Assertion
emptyRecord =
    let script = do
            name <- makeEmptyRecord "foo"
            x <- lookupName name
            return (name, x)

        continue (name, n) = do
            -- assertEqual "" (Just (P r :=>: REMPTY)) n
            assertEqual "" [("foo", 1)] name
            -- assertEqual "" (DEFN REMPTY :<: RSIG) (refBody r)

    in runScript script continue


addLabel :: Assertion
addLabel =
    let script = do
            recName <- makeEmptyRecord "foo"
            goTo recName
            _   <- elabAddRecordLabel ("x", DUNIT)
            val <- elabAddRecordLabel ("y", DUNIT)

            return (val, recName)

        expectedDecl =  RCONS (RCONS REMPTY
                                     (TAG "x")
                                     (LK UNIT))
                              (TAG "y")
                              (LK UNIT)

        continue (val, ref) = do
            -- assertEqual "" (DEFN expectedDecl :<: RSIG) (refBody ref)
            assertEqual "" (expectedDecl :<: RSIG) val

    in runScript script continue


removeLabel :: Assertion
removeLabel =
    let script = do
            topName     <- makeEmptyRecord "removeTop"
            middleName  <- makeEmptyRecord "removeMiddle"
            bottomName  <- makeEmptyRecord "removeBottom"

            forM_ [topName, middleName, bottomName] $ \name -> do
                goTo name
                elabAddRecordLabel ("x", DUNIT)
                elabAddRecordLabel ("y", DUNIT)
                elabAddRecordLabel ("z", DUNIT)

            goTo topName
            top     :<: _ <- removeRecordLabel "z"

            goTo middleName
            middle  :<: _ <- removeRecordLabel "y"

            goTo bottomName
            bottom  :<: _ <- removeRecordLabel "x"

            return (top, middle, bottom)

        continue (top, middle, bottom) = do

            -- Really, these tests are too specific. I don't think the order of
            -- the tags should matter. We really just want to know which are
            -- present.
            assertEqual "top"
                (RCONS (RCONS REMPTY
                              (TAG "x")
                              (LK UNIT))
                       (TAG "y")
                       (LK UNIT))
                top

            assertEqual "middle"
                (RCONS (RCONS REMPTY
                              (TAG "x")
                              (LK UNIT))
                       (TAG "z")
                       (LK UNIT))
                middle

            assertEqual "bottom"
                (RCONS (RCONS REMPTY
                              (TAG "y")
                              (LK UNIT))
                       (TAG "z")
                       (LK UNIT))
                bottom

    in runScript script continue


removeMissing :: Assertion
removeMissing =
    let script = do
            missingName <- makeEmptyRecord "removeMissing"
            goTo missingName

            elabAddRecordLabel ("x", DUNIT)
            elabAddRecordLabel ("y", DUNIT)
            elabAddRecordLabel ("z", DUNIT)

            removeRecordLabel "w"

    in assertThrows "remove missing label" script




tests :: TestTree
tests = testGroup "records"
    [ testCase "empty record" emptyRecord
    , testCase "add record label" addLabel
    , testCase "remove record label" removeLabel
    , testCase "remove missing record label" removeMissing
    ]
