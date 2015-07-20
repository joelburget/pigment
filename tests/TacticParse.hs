{-# LANGUAGE TypeOperators, OverloadedStrings #-}

module TacticParse (tests) where

import qualified Data.List as L
import Data.Monoid as M
import qualified Data.Text as T

import Test.Tasty
import Test.Tasty.HUnit

import Cochon.CommandLexer
import Cochon.Model
import Cochon.Tactics
import DisplayLang.DisplayTm
import DisplayLang.Lexer
import DisplayLang.Name
import DisplayLang.Scheme
import Elaboration.Elaborator
import Evidences.Tm
import Kit.Parsley
import ProofState.Edition.ProofContext

import Debug.Trace

assertEqEnough :: String -> TacticResult -> TacticResult -> Assertion
assertEqEnough str r1 r2 = assertBool str (eqEnough r1 r2)

assertParseAs :: CochonTactic -> String -> TacticResult -> Assertion
assertParseAs tac input result =
    case parse tokenize input of
        Left tf -> assertFailure (show tf)
        Right tokens -> case parse (parseTactic (ctDesc tac)) tokens of
            Left pf -> assertFailure (show pf)
            Right result' ->
                let msg = unlines
                        [ "parse results match:"
                        , showEnough result
                        , showEnough result'
                        ]
                in assertEqEnough msg result result'

listEqEnough :: [TacticResult] -> [TacticResult] -> Bool
listEqEnough xs ys =
    length xs == length ys &&
    (getAll $ mconcat $ map M.All $ zipWith eqEnough xs ys)

eqEnough :: TacticResult -> TacticResult -> Bool
eqEnough (TrName t1) (TrName t2) = t1 == t2
eqEnough TrKeyword TrKeyword = True
eqEnough TrPseudoKeyword TrPseudoKeyword = True
eqEnough (TrInArg tm1) (TrInArg tm2) = dInTmEq emptyContext SET tm1 tm2
eqEnough (TrExArg tm1) (TrExArg tm2) = dExTmEq emptyContext tm1 tm2
eqEnough (TrScheme s1) (TrScheme s2) = schemeEq emptyContext s1 s2
eqEnough (TrAlternative (Left l1)) (TrAlternative (Left l2)) = eqEnough l1 l2
eqEnough (TrAlternative (Right r1)) (TrAlternative (Right r2)) = eqEnough r1 r2
eqEnough (TrOption (Just j1)) (TrOption (Just j2)) = eqEnough j1 j2
eqEnough (TrOption Nothing) (TrOption Nothing) = True
eqEnough (TrRepeatZero xs) (TrRepeatZero ys) = listEqEnough xs ys
eqEnough (TrSequence xs) (TrSequence ys) = listEqEnough xs ys
eqEnough (TrBracketed br1 res1) (TrBracketed br2 res2) =
    br1 == br2 && eqEnough res1 res2
eqEnough (TrSep xs) (TrSep ys) = listEqEnough xs ys
eqEnough _ _ = False

schemeEq :: ProofContext -> Scheme DInTmRN -> Scheme DInTmRN -> Bool
schemeEq ctx (SchType s1) (SchType s2) = dInTmEq ctx SET s1 s2
schemeEq ctx (SchExplicitPi (name1 :<: sch1) sch1')
             (SchExplicitPi (name2 :<: sch2) sch2')
    =  name1 == name2
    && schemeEq ctx sch1  sch2
    && schemeEq ctx sch1' sch2'
schemeEq ctx (SchImplicitPi (name1 :<: tm1) sch1)
             (SchImplicitPi (name2 :<: tm2) sch2)
    =  name1 == name2
    && dInTmEq  ctx SET tm1  tm2
    && schemeEq ctx     sch1 sch2
schemeEq _ _ _ = False

dExTmEq :: ProofContext -> DExTmRN -> DExTmRN -> Bool
dExTmEq ctx tm1 tm2 =
    let x = do
              ((_ :=>: v1) :<: _, _) <- runProofState (elabInfer' tm1) ctx
              ((_ :=>: v2) :<: _, _) <- runProofState (elabInfer' tm2) ctx
              return (v1, v2)
    in case x of
           Right (tm1, tm2) -> tm1 == tm2
           Left err -> traceShow err False

dInTmEq :: ProofContext -> TY -> DInTmRN -> DInTmRN -> Bool
dInTmEq ctx ty tm1 tm2 =
    let x = do
              (_ :=>: v1, _) <- runProofState (elaborate' (ty :>: tm1)) ctx
              (_ :=>: v2, _) <- runProofState (elaborate' (ty :>: tm2)) ctx
              return (v1, v2)
    in case x of
           Right (tm1, tm2) -> tm1 == tm2
           Left err -> traceShow err False

showEnough :: TacticResult -> String
showEnough (TrName t1) = "TrName " ++ T.unpack t1
showEnough TrKeyword = "TrKeyword"
showEnough TrPseudoKeyword = "TrPseudoKeyword"
showEnough (TrInArg t) = "TrInArg (" ++ show t ++ ")"
showEnough (TrExArg t) = "TrEnArg (" ++ show t ++ ")"
showEnough (TrScheme s) = "TrScheme (" ++ show s ++ ")"
showEnough (TrAlternative (Left l)) = "TrAlternative Left " ++ showEnough l
showEnough (TrAlternative (Right r)) = "TrAlternative Right " ++ showEnough r
showEnough (TrOption (Just j)) = "TrOption " ++ showEnough j
showEnough (TrOption Nothing) = "TrOption Nothing"
showEnough (TrRepeatZero xs) = "TrRepeatZero [" ++ concat (L.intersperse ", " (map showEnough xs)) ++ "]"
showEnough (TrSequence xs) = "TrSequence ["     ++ concat (L.intersperse ", " (map showEnough xs)) ++ "]"
showEnough (TrBracketed br res) = "TrBracketed " ++ show br ++ " " ++ showEnough res
showEnough (TrSep xs) = "TrSep " ++ show (map showEnough xs)

nullaryTac :: CochonTactic
nullaryTac = nullaryCT "null" Historic undefined "test nullary tactic"

showTac :: CochonTactic
showTac = unaryStringCT "show" undefined "show test tactic"

nullaryTacParse :: Assertion
nullaryTacParse = do
    assertParseAs nullaryTac "" (TrSequence [])
    assertParseAs showTac "state"
        (TrSequence [ TrName "state" ])

letTacParse :: Assertion
letTacParse = do
    assertParseAs letTac "A : Set"
        (TrSequence [ TrName "A", TrScheme (SchType DSET)])

    assertParseAs letTac "A (m : Set) : Set -> Set"
        (TrSequence
          [ TrName "A"
          , TrScheme (SchExplicitPi
              ("m" :<: SchType DSET)
              (SchType (DPI DSET (DLK DSET)))
            )
         ]
        )

tests :: TestTree
tests = testGroup "TacticParse"
    [ testCase "nullaryCT" nullaryTacParse
    , testCase "let parsing" letTacParse
    ]
