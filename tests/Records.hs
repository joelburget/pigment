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


printProofState :: ProofState ()
printProofState = do
    s <- prettyProofState
    elabTrace s


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
            _   <- elabAddRecordLabel recName ("x", DUNIT)
            val <- elabAddRecordLabel recName ("y", DUNIT)
            -- goRoot

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
                elabAddRecordLabel name ("x", DUNIT)
                elabAddRecordLabel name ("y", DUNIT)
                elabAddRecordLabel name ("z", DUNIT)

            top     :<: _ <- removeRecordLabel topName "z"
            middle  :<: _ <- removeRecordLabel middleName "y"
            bottom  :<: _ <- removeRecordLabel bottomName "x"

            return (top, middle, bottom)

        continue (top, middle, bottom) = do

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

            elabAddRecordLabel missingName ("x", DUNIT)
            elabAddRecordLabel missingName ("y", DUNIT)
            elabAddRecordLabel missingName ("z", DUNIT)

            removeRecordLabel missingName "w"

    in assertThrows "remove missing label" script




tests :: TestTree
tests = testGroup "records"
    [ testCase "empty record" emptyRecord
    , testCase "add record label" addLabel
    , testCase "remove record label" removeLabel
    , testCase "remove missing record label" removeMissing
    ]
