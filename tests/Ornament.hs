{-# LANGUAGE PatternSynonyms #-}
module Ornament where

import Test.Tasty
import Test.Tasty.HUnit

import Evidences.Tm
import Evidences.Ornament


-- pattern RET i = C (Ornament (Ret i))
-- pattern ARG a f = C (Ornament (Arg a f))
-- pattern REC i d = C (Ornament (Rec i d))


tests :: TestTree
tests = testGroup "Ornament"

    [ testGroup "nat"
        [
        ]
    ]
