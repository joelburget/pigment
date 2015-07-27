{-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, PatternSynonyms,
    OverloadedStrings #-}

module Tactics.Record where

import DisplayLang.DisplayTm
import DisplayLang.Name
import Elaboration.Elaborator
import Evidences.Tm
import Evidences.Mangler
import Kit.BwdFwd
import NameSupply.NameSupplier
import NameSupply.NameSupply
import ProofState.Edition.GetSet
import ProofState.Edition.Navigation
import ProofState.Edition.ProofContext
import ProofState.Edition.ProofState
import ProofState.Edition.Scope
import ProofState.Interface.Module
import ProofState.Interface.Search
import ProofState.Interface.Solving
import ProofState.Interface.Definition
import ProofState.Structure.Developments

import Debug.Trace
import Kit.Trace
import Cochon.PrettyProofState

-- What things do we need:
--
-- create a label
--
-- create an empty record sig
-- add a label to a record sig
-- remove a label from a record sig
-- modify a label in a record sig
--
--
-- instantiate a record


makeEmptyRecord :: String -> ProofState Name
makeEmptyRecord name = freshRef (name :<: RSIG) $ \ref -> do
    nsupply <- askNSupply
    let meta = Metadata False "" False
        ref' = refName ref := DEFN REMPTY :<: RSIG
        dev = Dev { devEntries       =  B0
                  , devTip           =  Defined REMPTY (RSIG :=>: RSIG)
                  , devNSupply       =  freshNSpace nsupply name
                  , devSuspendState  =  SuspendNone }
    putEntryAbove $ EDEF ref' (mkLastName ref') LETG dev RSIG AnchNo emptyMetadata
    return $ refName ref


-- TODO non-elab version!
-- XXX ref doesn't get updated with new defn... what do refs actually mean?
elabAddRecordLabel :: (String, DInTmRN)
                   -> ProofState (VAL :<: TY)
elabAddRecordLabel (labelName, labelDTy) = do
    CDefinition _ ref lastN _ anch meta <- getCurrentEntry

    _ :=>: labelTy <- elaborate' (SET :>: labelDTy)

    let name = refName ref
        DEFN tm :<: RSIG = refBody ref
        recTm = RCONS
            -- this is the old record...
            tm
            -- ... with the addition of the new label...
            (TAG labelName)
            -- ... pointing to this type
            (LK labelTy)
        newRef = name := DEFN recTm :<: RSIG

    putCurrentEntry $ CDefinition LETG newRef lastN RSIG anch meta
    putDevTip $ Defined recTm (RSIG :=>: RSIG)

    return (recTm :<: RSIG)


removeHelper :: INTM -> String -> Maybe INTM
removeHelper (RCONS inner (TAG tagName) sigma) removeName
    | tagName == removeName
    = Just inner
    | otherwise
    = do inner' <- removeHelper inner removeName
         return $ RCONS inner' (TAG tagName) sigma
-- TODO don't throw!
removeHelper REMPTY removeName = Nothing -- error $ "couldn't remove " ++ removeName


removeRecordLabel :: String
                  -> ProofState (VAL :<: TY)
removeRecordLabel removeName = do
    CDefinition _ ref lastN _ anch meta <- getCurrentEntry
    let DEFN tm :<: RSIG = refBody ref

    case removeHelper tm removeName of
        Just newTm -> do
            let newRef = (refName ref) := DEFN newTm :<: RSIG

            putCurrentEntry $ CDefinition LETG newRef lastN RSIG anch meta
            putDevTip $ Defined newTm (RSIG :=>: RSIG)
            return (newTm :<: RSIG)
        Nothing -> throwDTmStr $ "cannot remove label " ++ removeName
