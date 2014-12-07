\section{Main}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Main where

> import Control.Monad.State

> import Kit.BwdFwd

> import ProofState.Edition.ProofContext

> import Tactics.Information

> import Cochon.Cochon

> import DisplayLang.Lexer

%endif

> main :: IO ()
> main = do
>     forM_ (enumFromTo minBound maxBound :: [Keyword]) $ \x -> do
>         print x
>         print $ fromEnum x
>     -- cochon emptyContext
