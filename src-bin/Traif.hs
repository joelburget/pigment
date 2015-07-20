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
import Distillation.ShowPity
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

import qualified IPPrint
import qualified Language.Haskell.HsColour as HsColour
import qualified Language.Haskell.HsColour.Colourise as HsColour
import qualified Language.Haskell.HsColour.Output as HsColour

myColourPrefs = HsColour.defaultColourPrefs { HsColour.conid = [HsColour.Foreground HsColour.Yellow, HsColour.Bold], HsColour.conop = [HsColour.Foreground HsColour.Yellow], HsColour.string = [HsColour.Foreground HsColour.Green], HsColour.char = [HsColour.Foreground HsColour.Cyan], HsColour.number = [HsColour.Foreground HsColour.Red, HsColour.Bold], HsColour.layout = [HsColour.Foreground HsColour.White], HsColour.keyglyph = [HsColour.Foreground HsColour.White] }
myPrint = putStrLn . HsColour.hscolour (HsColour.TTYg HsColour.XTerm256Compatible) myColourPrefs False False "" False . IPPrint.pshow

-- elabLet :: (String :<: Scheme DInTmRN) -> ProofState (EXTM :=>: VAL)
-- elabProgram :: [String] -> ProofState (EXTM :=>: VAL)
-- elabData :: String
--          -> [ (String , DInTmRN) ]
--          -> [ (String , DInTmRN) ]
--          -> ProofState (EXTM :=>: VAL)


script :: ProofState ()
script = do
  elabLet ("S" :<: SchType DSET)
  _ <- many goOut
  return ()

script1 :: ProofState ()
script1 = do
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
            Left err -> putStrLn err
            Right (view, ctx) -> do
              myPrint ctx
              putStrLn "\n\n"
              putStrLn view
    val `catch` \ (ex :: PiTyException) -> showPity ex

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
