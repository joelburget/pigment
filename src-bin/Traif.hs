{-# LANGUAGE PatternSynonyms, ScopedTypeVariables #-}
module Traif (main) where

import Control.Applicative (many, optional)
import Control.Arrow (left)
import Control.Exception
import Control.Monad.State
import Text.PrettyPrint.HughesPJ

import Kit.BwdFwd
import DisplayLang.DisplayTm
import DisplayLang.Lexer
import DisplayLang.Name
import DisplayLang.PrettyPrint
import DisplayLang.Scheme
import Distillation.Distiller
import Elaboration.Error
import Elaboration.Elaborator
import Evidences.Operators
import Evidences.Tm
import NameSupply.NameSupply
import ProofState.Edition.GetSet
import ProofState.Edition.Navigation
import ProofState.Edition.ProofContext
import ProofState.Edition.ProofState
import ProofState.Interface.Module
import ProofState.Interface.ProofKit
import ProofState.Interface.Search
import ProofState.Interface.Solving
import ProofState.Structure.Developments
import ProofState.Structure.Entries
import Tactics.Data
import Tactics.ProblemSimplify

-- elabLet :: (String :<: Scheme DInTmRN) -> ProofState (EXTM :=>: VAL)
-- elabProgram :: [String] -> ProofState (EXTM :=>: VAL)
-- elabData :: String
--          -> [ (String , DInTmRN) ]
--          -> [ (String , DInTmRN) ]
--          -> ProofState (EXTM :=>: VAL)

script :: ProofState ()
script = do
    makeModule DevelopModule "Math"
    goIn
    makeModule DevelopModule "Algebra"
    goIn

    -- let scheme = SchExplicitPi ("x" :<: SchType DSET) (SchType DSET)
    let scheme = SchType DSET
    elabLet ("ring" :<: scheme)
    optional problemSimplify
    _ <- many goOut
    return ()


script'' :: ProofState ()
script'' = do

    _ <- elabData "Foo" [] []
    _ <- many goOut
    return ()

script' :: ProofState ()
script' = do
        -- result of `parse pDInTm [Identifier "Nat"]`
    let nat = DN (DP [("Nat", Rel 0)] ::$ [])
        -- result of `parse pDInTm [Identifier "Nat", Keyword KwArr, Identifier "Nat" ]`
        natToNat = DC (Pi nat (DL (DK nat)))

    -- data Nat := ('z : Nat) ; ('s : Nat -> Nat) ;
    _ <- elabData "Nat"
             -- parameters
             []
             -- schemes
             [ ("z", nat), ("s", natToNat) ]

    -- let plus (m : Nat)(n : Nat) : Nat ;
    let plusScheme = SchExplicitPi
                         ("m" :<: SchType nat)
                         (SchExplicitPi
                             ("n" :<: SchType nat)
                             (SchType nat)
                         )
    _ <- elabLet ("plus" :<: plusScheme)

    -- root
    _ <- many goOut
    return ()

main' :: Either String (String, ProofContext)
main' =
    let runner :: ProofState String
        runner = script >> prettyProofState
    in runTraifProofState runner emptyContext

main :: IO ()
main = do
    let val = case main' of
            Left err -> err
            Right (view, ctx) -> view ++ "\n\n" ++ show ctx
    putStrLn val `catch` \ (ex :: PiTyException) -> showPity ex

showPity :: PiTyException -> IO ()
showPity (PiTyException name ty) = do
    putStrLn "Caught pity error:"
    putStrLn $ "name: " ++ name
    let val = case runTraifProofState (prettyHere (SET :>: ty)) emptyContext of
                  Left err -> err
                  Right (doc, _) -> renderHouseStyle doc
    putStrLn $ "type: " ++ val
    putStrLn "\n"

-- Given a proof state command and a context, we can run the command with
-- `runProofState` to produce a message (either the response from the command
-- or the error message) and `Maybe` a new proof context.
runTraifProofState
    :: ProofState a
    -> ProofContext
    -> Either String (a, ProofContext)
runTraifProofState m loc =
    let result = runStateT (m `catchStack` catchUnprettyErrors) loc
    in left show result
