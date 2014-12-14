Main
====

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Main where

> import ProofState.Edition.ProofContext
> import Cochon.Cochon

> main :: IO ()
> main = cochon emptyContext
