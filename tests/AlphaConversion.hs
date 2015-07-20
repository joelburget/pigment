module AlphaConversion (tests) where

import Test.Tasty
import Test.Tasty.HUnit

import Evidences.Eval
import Evidences.Tm


testTxtSub :: Assertion
testTxtSub = do
    assertEqual "" "wombat" (txtSub [('c', "womb")] "cat")
    assertEqual "" "" (txtSub [('y', "")] "yyy")
    assertEqual "" "dog" (txtSub [('a', "alpha"), ('b', "beta")] "dog")

testNaming :: Assertion
testNaming = do
    let monks = (NP ([("monks", 0)] := FAKE :<: SET))
        noName = (NP ([("", 0)] := FAKE :<: SET))

    -- empty string base cases
    assertEqual "" [] (naming "" monks [])
    assertEqual "" [] (naming "xys" noName [])

    -- do nothing if free and bound match
    assertEqual "" [] (naming "monks" monks [])

    let abcdeMonks =
          [ ('a', "m")
          , ('b', "o")
          , ('c', "n")
          , ('d', "k")
          , ('e', "s")
          ]

    -- match everything up
    assertEqual "" abcdeMonks (naming "abcde" monks [])
    assertEqual "" (abcdeMonks ++ abcdeMonks) (naming "abcde" monks abcdeMonks)

    assertEqual ""
      [ ('p', "m")
      -- , ('o', "o")
      , ('e', "n")
      , ('t', "k")
      -- , ('s', "s")
      ]
      (naming "poets" monks [])

    assertEqual "" [('x', "sknom")] (naming "x" monks [])

    -- example
    assertEqual "" [('x', "nom"), ('y', "k")] (naming "xys" monks [])

tests :: TestTree
tests = testGroup "alpha conversion"
    [ testCase "txtSub" testTxtSub
    , testCase "naming" testNaming
    ]
