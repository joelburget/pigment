{-# LANGUAGE TypeOperators, OverloadedStrings #-}

module TacticParse (tests) where

import Data.Monoid
import qualified Data.Text as T

import Test.Tasty
import Test.Tasty.HUnit

import Cochon.CommandLexer
import Cochon.Model
import Cochon.Tactics
import DisplayLang.Lexer
import Kit.Parsley

assertEqEnough :: String -> TacticResult -> TacticResult -> Assertion
assertEqEnough str r1 r2 = assertBool str (eqEnough r1 r2)

assertParseAs :: CochonTactic -> String -> TacticResult -> Assertion
assertParseAs tac input result =
    case parse tokenize input of
        Left tf -> assertFailure (show tf)
        Right tokens -> case parse (parseTactic (ctDesc tac)) tokens of
            Left pf -> assertFailure (show pf)
            Right result' ->
                assertEqEnough ("parse results match " ++ showEnough result ++ showEnough result') result result'

listEqEnough :: [TacticResult] -> [TacticResult] -> Bool
listEqEnough xs ys =
    length xs == length ys &&
    (getAll $ mconcat $ map All $ zipWith eqEnough xs ys)

eqEnough :: TacticResult -> TacticResult -> Bool
eqEnough (TrName t1) (TrName t2) = t1 == t2
eqEnough TrKeyword TrKeyword = True
eqEnough TrPseudoKeyword TrPseudoKeyword = True
eqEnough (TrInArg _) (TrInArg _) = True
eqEnough (TrExArg _) (TrExArg _) = True
eqEnough (TrScheme _) (TrScheme _) = True
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

showEnough :: TacticResult -> String
showEnough (TrName t1) = "TrName " ++ T.unpack t1
showEnough TrKeyword = "TrKeyword"
showEnough TrPseudoKeyword = "TrPseudoKeyword"
showEnough (TrInArg _) = "TrInArg"
showEnough (TrExArg _) = "TrEnArg"
showEnough (TrScheme _) = "TrScheme"
showEnough (TrAlternative (Left l)) = "TrAlternative Left " ++ showEnough l
showEnough (TrAlternative (Right r)) = "TrAlternative Right " ++ showEnough r
showEnough (TrOption (Just j)) = "TrOption " ++ showEnough j
showEnough (TrOption Nothing) = "TrOption Nothing"
showEnough (TrRepeatZero xs) = "TrRepeatZero " ++ show (map showEnough xs)
showEnough (TrSequence xs) = "TrSequence " ++ show (map showEnough xs)
showEnough (TrBracketed br res) = "TrBracketed " ++ show br ++ " " ++ showEnough res
showEnough (TrSep xs) = "TrSep " ++ show (map showEnough xs)

nullaryTac :: CochonTactic
nullaryTac = nullaryCT "null" Historic undefined "test nullary tactic"

showTac :: CochonTactic
showTac = unaryStringCT "show" undefined "show test tactic"

nullaryTacParse :: Assertion
nullaryTacParse = do
    assertParseAs nullaryTac "null" TrPseudoKeyword
    assertParseAs showTac "show state"
        (TrSequence [ TrPseudoKeyword, TrName "state" ])

tests :: TestTree
tests = testGroup "TacticParse"
    [ testCase "nullaryCT" nullaryTacParse
    ]
