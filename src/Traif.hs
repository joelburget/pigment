{-# LANGUAGE PatternSynonyms, TypeOperators #-}
module Traif (traif) where

import Control.Applicative (many, optional, (<|>))
import Control.Arrow (left)
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
import Evidences.Tm
import NameSupply.NameSupply
import ProofState.Edition.GetSet
import ProofState.Edition.Navigation
import ProofState.Edition.ProofContext
import ProofState.Edition.ProofState
import ProofState.Interface.ProofKit
import ProofState.Structure.Developments
import ProofState.Structure.Entries
import Tactics.Data

import Tactics.SpecialTactics
import Tactics.ProblemSimplify
import ProofState.Interface.Search
import Kit.Trace
import Debug.Trace
import Kit.Parsley
import DisplayLang.TmParse
import Elaboration.Scheduler
import Elaboration.ElabProb
import qualified ProofState.Interface.Solving as Solving

-- elabLet :: (String :<: Scheme DInTmRN) -> ProofState (EXTM :=>: VAL)
-- elabProgram :: [String] -> ProofState (EXTM :=>: VAL)
-- elabData :: String
--          -> [ (String , DInTmRN) ]
--          -> [ (String , DInTmRN) ]
--          -> ProofState (EXTM :=>: VAL)

script :: ProofState ()
script = do
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

parseLet :: String -> ProofState (EXTM :=>: VAL)
parseLet decl =
    let Right (_:(Identifier name):declTokens) = parse tokenize decl
        Right scheme = parse pScheme declTokens
    in elabLet (name :<: scheme)

parseRet :: String -> ProofState (EXTM :=>: VAL)
parseRet impl =
    let Right (_:implTokens) = parse tokenize impl
        Right intm = parse pDInTm implTokens
          -- elabGiveNext (traceShowId $ DLRET intm)
    in do
          tm' <- elabGive' (DLRET intm)
          elabTrace (show tm')
          startScheduler
          nextGoal <|> goOut
          return tm'


traceState :: ProofState ()
traceState = do
    str <- prettyProofState
    elabTrace $ "proof state:\n" ++ str ++ "\n"

newScript :: ProofState ()
newScript = do
    parseLet "let f {A : Set}{B : Set}(a : A)(b : A -> B) : B"

    traceState

    optional problemSimplify
    -- optional seekGoal

    traceState

    -- parseRet "= b a"
    -- auto

    parseRet "= b ?"
    optional problemSimplify

    traceState

    parseRet "= a"
    optional problemSimplify

    -- Solving.done

    traceState

    return ()


traif :: IO ()
traif = do
    let runner :: ProofState String
        runner = newScript >> prettyProofState
        val :: String
        val = case runTraifProofState runner emptyContext of
            Left err -> err
            Right (view, _) -> view

    putStrLn val

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

prettyProofState :: ProofState String
prettyProofState = do
    inScope <- getInScope
    me <- getCurrentName
    d <- prettyPS inScope me
    return (renderHouseStyle d)

prettyPS :: Entries -> Name -> ProofState Doc
prettyPS aus me = do
        es <- replaceEntriesAbove B0
        cs <- putBelowCursor F0
        case (es, cs) of
            (B0, F0)  -> prettyEmptyTip
            _   -> do
                d <- prettyEs empty (es <>> F0)
                d' <- case cs of
                    F0  -> return d
                    _   -> do
                        d'' <- prettyEs empty cs
                        return (d $$ text "---" $$ d'')
                tip <- prettyTip
                putEntriesAbove es
                _ <- putBelowCursor cs
                return (lbrack <+> d' $$ rbrack <+> tip)
 where
    prettyEs :: Doc -> Fwd (Entry Bwd) -> ProofState Doc
    prettyEs d F0         = return d
    prettyEs d (e :> es) = do
        putEntryAbove e
        ed <- prettyE e
        prettyEs (d $$ ed) es

    prettyE (EPARAM (_ := DECL :<: ty) (x, _) k _ anchor _)  = do
        ty' <- bquoteHere ty
        tyd <- prettyHereAt (pred ArrSize) (SET :>: ty')
        return (prettyBKind k
                 (text x  <+> (brackets $ brackets $ text $ show anchor)
                          <+> kword KwAsc
                          <+> tyd))

    prettyE e = do
        goIn
        d <- prettyPS aus me
        goOut
        return (sep  [  text (fst (entryLastName e))
                        <+> (brackets $ brackets $ text $ show $ entryAnchor e)
                     ,  nest 2 d <+> kword KwSemi
                     ])

    prettyEmptyTip :: ProofState Doc
    prettyEmptyTip = do
        tip <- getDevTip
        case tip of
            Module -> return (brackets empty)
            _ -> do
                tip <- prettyTip
                return (kword KwDefn <+> tip)

    prettyTip :: ProofState Doc
    prettyTip = do
        tip <- getDevTip
        case tip of
            Module -> return empty
            Unknown (ty :=>: _) -> do
                hk <- getHoleKind
                tyd <- prettyHere (SET :>: ty)
                return (prettyHKind hk <+> kword KwAsc <+> tyd)
            Suspended (ty :=>: _) prob -> do
                hk <- getHoleKind
                tyd <- prettyHere (SET :>: ty)
                probd <- prettyProb prob
                return (probd <+> prettyHKind hk <+> kword KwAsc <+> tyd)
            Defined tm (ty :=>: tyv) -> do
                tyd <- prettyHere (SET :>: ty)
                tmd <- prettyHereAt (pred ArrSize) (tyv :>: tm)
                return (tmd <+> kword KwAsc <+> tyd)

    prettyHKind :: HKind -> Doc
    prettyHKind Waiting     = text "?"
    prettyHKind Hoping      = text "HOPE?"
    prettyHKind (Crying s)  = text ("CRY <<" ++ s ++ ">>")

    prettyProb :: ElabProb x -> ProofState Doc
    prettyProb (ElabDone (intm :=>: val)) = return (text "DONE")
    prettyProb ElabHope = return (text "HOPE")
    prettyProb (ElabProb dintm) = return (text "ELABPROB")
    prettyProb (ElabInferProb extm) = return (text "ELABINFERPROB")
    prettyProb (WaitCan (intm :=>: mayVal) prob) = return (text "WAITCAN")
    prettyProb (WaitSolve x (intm :=>: mayVal) prob) = return (text "WAITSOLVE")
    prettyProb (ElabSchedule prob) = return (text "SCHEDULE")
