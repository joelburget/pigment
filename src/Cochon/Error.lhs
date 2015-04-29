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

> -- Given a proof state command and a context, we can run the command with
> -- `runProofState` to produce a message (either the response from the
> -- command or the error message) and `Maybe` a new proof context.
> runProofState
>     :: ProofState a
>     -> ProofContext
>     -> Either TermReact (a, ProofContext)
> runProofState m loc =
>     let result = runStateT (m `catchStack` catchUnprettyErrors) loc
>     in left reactStackError result

Pretty-printing the stack trace
-------------------------------

> reactStackError :: StackError DInTmRN -> TermReact
> reactStackError (StackError errors) = div_ [ class_ "stack-error" ] $ do
>     div_ "Error:"
>     ul_ [ class_ "stack-error-list" ] $
>         forM_ errors $ \error ->
>             li_ [ class_ "stack-error-item" ] $
>                 mapM_ reactErrorTok error

> reactErrorTok :: ErrorTok DInTmRN -> TermReact
> reactErrorTok (StrMsg s)           = fromString s
> reactErrorTok (ErrorTm (v :<: _))  = reactify v
> reactErrorTok (ErrorCan   v)       = reactify v
> reactErrorTok (ErrorElim  e)       = reactify e
> reactErrorTok (ErrorREF ref)       = fromString $ show ref
> reactErrorTok (ErrorVAL (v :<: _)) = do
>     "ErrorVAL"
>     -- reactBrackets Round (reactify v)
>     reactBrackets Round $ fromString $ show v
