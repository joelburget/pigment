Cochon error prettier
=====================

> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, PatternSynonyms #-}

> module Cochon.Error where

> import Control.Arrow
> import Control.Monad.State
> import Text.PrettyPrint.HughesPJ

> import Evidences.Tm
> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.PrettyPrint
> import ProofState.Edition.ProofContext
> import ProofState.Edition.ProofState
> import ProofState.Interface.ProofKit
> import Distillation.Distiller
> import Distillation.Moonshine

> -- Given a proof state command and a context, we can run the command with
> -- `runProofState` to produce a message (either the response from the
> -- command or the error message) and `Maybe` a new proof context.
> runProofState
>     :: ProofState a
>     -> ProofContext
>     -> Either String (a, ProofContext)
> runProofState m loc =
>     let result = runStateT (m `catchStack` catchUnprettyErrors) loc
>     in left (renderHouseStyle . prettyStackError) result

Catching the gremlins before they leave `ProofState`
----------------------------------------------------

> catchUnprettyErrors :: StackError DInTmRN -> ProofState a
> catchUnprettyErrors e = do
>     e' <- distillErrors e
>     throwStack e'

> distillErrors :: StackError DInTmRN -> ProofState (StackError DInTmRN)
> distillErrors (StackError e) =
>     StackError `fmap` sequence (fmap (sequence . fmap distillError) e)

> distillError :: ErrorTok DInTmRN -> ProofState (ErrorTok DInTmRN)
> distillError (ErrorVAL (v :<: mt)) = do
>     vTm   <- bquoteHere v
>     vDTm  <- case mt of
>         Just t   -> return . termOf =<< distillHere (t :>: vTm)
>         Nothing  -> liftErrorState DTIN (moonshine vTm)
>     return $ ErrorTm (vDTm :<: Nothing)
> distillError (ErrorTm (DTIN t :<: mt)) = do
>     d <- liftErrorState DTIN (moonshine t)
>     return $ ErrorTm (d :<: Nothing)
> distillError e = return e

Pretty-printing the stack trace
-------------------------------

> prettyStackError :: StackError DInTmRN -> Doc
> prettyStackError (StackError e) = vcat $
>     fmap (((text "Error:" <>) . hsep) . fmap prettyErrorTok) e

> prettyErrorTok :: ErrorTok DInTmRN -> Doc
> prettyErrorTok (StrMsg s)              = text s
> prettyErrorTok (ErrorTm    (v :<: _))  = pretty v maxBound
> prettyErrorTok (ErrorCan   v)  = pretty v maxBound
> prettyErrorTok (ErrorElim  e)  = pretty e maxBound

The following cases should be avoided as much as possible:

> prettyErrorTok (ErrorREF ref) = text $ show ref
> prettyErrorTok (ErrorVAL (v :<: _)) =
>     text "ErrorVAL" <> brackets (text (show v))
