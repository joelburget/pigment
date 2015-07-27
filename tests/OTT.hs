module OTT where

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


coeCase :: Can VAL -> Can VAL -> VAL -> VAL -> VAL -> Assertion
coeCase a b p t expected = case halfZip a b of
    Nothing -> assertFailure "couldn't halfzip"
    Just z -> case coerce z p t of
        Left neu -> assertFailure "couldn't coerce"
        Right val -> assertEqual "" val expected

-- take two types, a proof they're equal, and a value,
-- and the expected resulting value of the second type and the expected proof
-- it's equal to the original value
coehCase :: TY -> TY -> VAL -> VAL -> VAL -> VAL -> Assertion
coehCase s t q v expectedVal expectedProof =
    assertEqual "" (coeh s t q v) (expectedVal, expectedProof)

propEqCase :: (TY :>: VAL) -> (TY :>: VAL) -> VAL -> Assertion
propEqCase v1 v2 expected =
    assertEqual "<->" expected (v1 <-> v2)

tests :: TestTree
tests = testGroup "OTT"

    [ testGroup "coe"
        [ testCase "coe empty empty"
            (coeCase (EnumT NILE) (EnumT NILE) (PRF TRIVIAL) ABSURD ABSURD)
        , testCase "coe unit unit"
            (coeCase Unit Unit (PRF TRIVIAL) VOID VOID)
        , testCase "coe unit unit"
            (coeCase Unit Unit (BOX (Irr (INH UNIT))) TRIVIAL TRIVIAL)
        -- , testCase "coe bool bool"
        --     (coeCase Unit Unit (PRF TRIVIAL) TRIVIAL TRIVIAL)
        ]

    , testGroup "coeh"
        [ testCase "coeh" $

            -- bleh, this is not right
            coehCase
                SET SET (N $ P refl $:$ [A SET, A UNIT]) UNIT
                UNIT (N $ P refl $:$ [A SET, A UNIT])

        ]

    , testGroup "propositional equality operator"
        [ testCase "Empty <-> Empty ~> trivial" $
            assertEqual "<->" TRIVIAL $ (UNIT :>: VOID) <-> (UNIT :>: VOID)

        , testCase "Unit <-> Unit ~> trivial" $
            assertEqual "<->" TRIVIAL $ (SET :>: UNIT) <-> (SET :>: UNIT)

        , testCase "P <-> Q ~> (P => Q) and (Q => P)" $
            -- p and q are meaningless -- "a proof of this bound variable
            -- implies a proposition
            let p = IMP (PRF (INH (NV 0))) PROP
                q = IMP (PRF (INH (NV 1))) PROP

                -- but the important thing is that equality reduction turns it
                -- into a couple implications
                result = AND (IMP p q) (IMP q p)
            in assertEqual "<->" result $ (PROP :>: p) <-> (PROP :>: q)

        -- TODO(joel) - I'm really not sure this is right...
        , testCase "(P x Q) <-> (Q x P) ~> trivial" $
            let p = IMP (PRF (INH (NV 0))) PROP
                q = IMP (PRF (INH (NV 1))) PROP
                left = PAIR p q
                right = PAIR q p
                ty = PRF (AND PROP PROP)
                result = TRIVIAL

            in assertEqual "<->" result $ (ty :>: left) <-> (ty :>: right)

--         , testCase "(A -> B) <-> (A -> B) ~> ?" $
--             let a = NV 1
--                 b = NV 0
--                 aTy = NV 4
--                 bTy = NV 3
--                 lam = LAV "a" b
--                 arr = PI aTy (LK bTy)
--                 expected = ALL aTy $ L "s1" $
--                     ALL aTy $ "s2" $
--                         IMP (EQBLUE aTy :>: NV 1) (...
--             in assertEqual "<->" ABSURD $ (arr :>: lam) <-> (arr :>: lam)

        , testCase "Can <-> Can ~> absurd" $
            assertEqual "<->" ABSURD $ (SET :>: UNIT) <-> (SET :>: SET)
        ]
    ]
