{-# LANGUAGE TypeOperators, GADTs, KindSignatures,
    TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables, CPP #-}

module Main where

import ProofState.Edition.ProofContext

#ifdef __GHCJS__
import Cochon.Cochon

main :: IO ()
main = cochon emptyContext
#else
import Traif

main :: IO ()
main = putStrLn "here"
#endif
