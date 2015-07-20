module Distillation.ShowPity where

import Control.Arrow (left)
import Control.Monad.State
import Text.PrettyPrint.HughesPJ

import DisplayLang.PrettyPrint
import Distillation.Distiller
import Elaboration.Error
import Evidences.Operators
import Evidences.Tm
import ProofState.Edition.ProofContext
import ProofState.Edition.ProofState


runPityProofState
    :: ProofState a
    -> ProofContext
    -> Either String (a, ProofContext)
runPityProofState m loc =
    let result = runStateT (m `catchStack` catchUnprettyErrors) loc
    in left show result


showPity :: PiTyException -> String
showPity (PiTyException name ty) =
    let val = case runPityProofState (prettyHere (SET :>: ty)) emptyContext of
                  Left err -> err
                  Right (doc, _) -> renderHouseStyle doc
    in unlines
        [ "Caught pity error:"
        , "name: " ++ name
        , "type: " ++ val
        , "\n"
        ]
