Cochon error prettier
=====================

> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, PatternSynonyms, LiberalTypeSynonyms, OverloadedStrings  #-}

> module Cochon.Error where

> import Control.Arrow
> import Control.Monad.State
> import Data.String

> import React

> import Cochon.Model
> import Cochon.Reactify
> import Elaboration.Error
> import Evidences.Tm
> import DisplayLang.DisplayTm
> import DisplayLang.Lexer
> import DisplayLang.Name
> import DisplayLang.PrettyPrint
> import ProofState.Edition.ProofContext
> import ProofState.Edition.ProofState
> import ProofState.Interface.ProofKit
> import Distillation.Moonshine
