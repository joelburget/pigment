module Desc where

import Control.Monad

import Test.Tasty
import Test.Tasty.HUnit

import Cochon.Model
import Evidences.Eval
import Evidences.Operators
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


unitConstructors :: INTM
unitConstructors = CONSE (TAG "mkUnit") NILE


unitBranches :: INTM
unitBranches = PAIR (CONSTD UNIT) VOID


unitD :: INTM
unitD = SUMD unitConstructors $ L $ "constr" :. constrBind
    where constr = NV 0
          constrBind = N $
              switchDOp :@ [ unitConstructors, unitBranches, constr ]

unit :: INTM
unit = MU (Just (ANCHOR (TAG "Unit") SET ALLOWEDEPSILON)) unitD


natConstructors :: INTM
natConstructors = CONSE (TAG "zero") (CONSE (TAG "suc") NILE)

natBranches :: INTM
natBranches = PAIR
    (CONSTD UNIT)
    (PAIR IDD
          VOID)

natD :: INTM
natD = SUMD natConstructors $ L $ "constr" :. constrBind
    where constr = NV 0
          constrBind = N $
              switchDOp :@ [ natConstructors , natBranches , constr ]


nat :: INTM
nat = MU (Just (ANCHOR (TAG "Nat") SET ALLOWEDEPSILON)) natD


natREF :: REF
natREF = [("Primitive", 0), ("Nat", 0)] := DEFN nat :<: SET

natDREF :: REF
natDREF = [("Primitive", 0), ("NatD", 0)] := DEFN natD :<: desc

natConstructorsREF :: REF
natConstructorsREF = [("Primitive", 0), ("NatConstructors", 0)] :=
    DEFN natConstructors :<: enumU

natBranchesREF :: REF
natBranchesREF = [("Primitive", 0), ("NatBranches", 0)] :=
    DEFN natBranches :<: branchesOp @@ [natConstructors, LK nat]

ze :: INTM
ze = CON (PAIR ZE VOID)

suc :: INTM -> INTM
suc n = CON (PAIR (SU ZE) n)


tests :: TestTree
tests = testGroup "nat desc"
    [
    ]
