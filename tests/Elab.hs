module Elab where

import Control.Monad

import Test.Tasty
import Test.Tasty.HUnit

import Kit.MissingLibrary
import Cochon.Model
import Evidences.Eval
import Evidences.Tm
import Evidences.PropositionalEquality
import Evidences.Operators
import ProofState.Edition.ProofContext

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

import PigmentPrelude


tests :: TestTree
tests = testGroup "Elab"

    [ testGroup "elab monad"

        -- underscore -- "figure this out yourself"
        [ let continue (tm :=>: val) = do
                  assertEqual holeRef tm
                  assertEqual holeRef val

              holeRef = [("_", 0)] := HOLE Hoping :<: UNIT

          in runScript (elaborate' (UNIT :>: DU)) continue

        -- question mark -- "i don't know yet"
        , let continue (tm :=>: val) = do
                  assertEqual holeRef tm
                  assertEqual holeRef val

              holeRef = [("dunno", 0)] := HOLE Waiting :<: UNIT

          -- figure this out yourself
          in runScript (elaborate' (SET :>: DQ "dunno")) continue

        -- canonical term
        , let continue (tm :=>: val) = do
                  assertEqual VOID tm
                  assertEqual VOID val

          in runScript (elaborate' (UNIT :>: DVOID))

        -- constant lambda
        , let continue (tm :=>: val) = do
                  assertEqual (LK VOID) tm
                  assertEqual (LK VOID) val

              a = NV 0

          in runScript (elaborate' (ARR a UNIT) :>: DL (DK DVOID))
        ]
    ]
