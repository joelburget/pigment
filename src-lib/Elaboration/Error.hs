{-# LANGUAGE PatternSynonyms #-}
module Elaboration.Error where

import Text.PrettyPrint.HughesPJ

import Evidences.Tm
import DisplayLang.DisplayTm
import DisplayLang.PrettyPrint
import DisplayLang.Name
import Distillation.Distiller
import Distillation.Moonshine
import ProofState.Edition.ProofState
import ProofState.Interface.ProofKit


distillErrors :: StackError DInTmRN -> ProofState (StackError DInTmRN)
distillErrors (StackError e) =
    StackError `fmap` sequence (fmap (sequence . fmap distillError) e)


distillError :: ErrorTok DInTmRN -> ProofState (ErrorTok DInTmRN)
distillError (ErrorVAL (v :<: mt)) = do
    vDTm  <- case mt of
        Just t   -> return . termOf =<< distillHere (t :>: v)
        Nothing  -> liftErrorState DTIN (moonshine v)
    return $ ErrorTm (vDTm :<: Nothing)
distillError (ErrorTm (DTIN t :<: mt)) = do
    d <- liftErrorState DTIN (moonshine t)
    return $ ErrorTm (d :<: Nothing)
distillError e = return e


prettyStackError :: StackError DInTmRN -> Doc
prettyStackError (StackError e) = vcat $
    fmap (((text "Error:" <>) . hsep) . fmap prettyErrorTok) e


prettyErrorTok :: ErrorTok DInTmRN -> Doc
prettyErrorTok (StrMsg s)              = text s
prettyErrorTok (ErrorTm    (v :<: _))  = pretty v maxBound
prettyErrorTok (ErrorCan   v)  = pretty v maxBound
prettyErrorTok (ErrorElim  e)  = pretty e maxBound

-- The following cases should be avoided as much as possible:
prettyErrorTok (ErrorREF ref) = text $ show ref
prettyErrorTok (ErrorVAL (v :<: _)) =
    text "ErrorVAL" <> brackets (text (show v))


-- Catching the gremlins before they leave `ProofState`

catchUnprettyErrors :: StackError DInTmRN -> ProofState a
catchUnprettyErrors e = do
    e' <- distillErrors e
    throwStack e'
