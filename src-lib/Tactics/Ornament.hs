module Tactics.Ornament where

import Control.Applicative
import Control.Error
import Control.Monad.Identity
import Data.Functor.Constant
import Data.Monoid hiding (All)
import Data.Traversable

import Kit.BwdFwd
import Kit.MissingLibrary
import Evidences.Tm
import Evidences.Mangler
import Evidences.Eval
import Evidences.Operators
import Evidences.DefinitionalEquality
import NameSupply.NameSupplier
import NameSupply.NameSupply
import ProofState.Structure.Developments
import ProofState.Edition.Scope
import ProofState.Edition.ProofState
import ProofState.Edition.GetSet
import ProofState.Edition.Navigation
import ProofState.Edition.FakeRef
import ProofState.Edition.ProofContext
import ProofState.Interface.ProofKit
import ProofState.Interface.Module
import ProofState.Interface.Definition
import ProofState.Interface.Parameter
import ProofState.Interface.Solving
import Elaboration.Elaborator
import DisplayLang.DisplayTm
import DisplayLang.Name


-- on parameters vs indexes:
--
-- > If an argument to a type constructor does not change in the data
-- > constructor declarations, Idris considers it a parameter, otherwise an
-- > index.



emptyData :: String -> ProofState Name
emptyData name = freshRef (name :<: SET) $ \ref -> do
    nsupply <- askNSupply

    let result :: TYDESC
        result = TyDesc [] []

    let meta = Metadata False "" False
        ref' = refName ref := DEFN result :<: SET -- XXX get right type
        dev = Dev { devEntries       =  B0
                  , devTip           =  Defined REMPTY (SET :=>: SET)
                  , devNSupply       =  freshNSpace nsupply name
                  , devSuspendState  =  SuspendNone }
    putEntryAbove $ EDEF ref' (mkLastName ref') LETG dev SET AnchNo emptyMetadata
    return $ refName ref


-- XXX huge TODO:
-- figure out how to handle changes when this thing is in use
addTypeParam :: (String, DInTmRN) -> ProofState REF -- (EXTM :=>: VAL)
addTypeParam (name, dTy) = do
    CDefinition _ ref lastN _ anch meta <- getCurrentEntry

    _ :=>: ty <- elaborate' (SET :>: dTy)

    let name = refName ref
        newTm = undefind

    putCurrentEntry $ CDefinition LETG newRef lastN RSIG anch meta
    putDevTip $ Defined newTm (RSIG :=>: RSIG)


addConstructor :: String
               -- ^ Name of the type constructor
               --
               -- TODO(joel) I'm sure this can be recovered reliably from the
               -- context
               -> (String, DInTmRN)
               -- ^ Name and scheme of constructor to build
               --
               -- TODO(joel) curry?
               -> ProofState ()
addConstructor tyName (name, scheme) = do
    CDefinition LETG ref@(n := (_ :<: ty)) _ _ anch meta <- getCurrentEntry

    let parameters = undefined
        tyTyTODO = undefined
        elims = map (A . NP . paramRef) parameters

    -- first build the description
    elabCons tyName tyTyTODO elims (name, scheme)

    -- now build the actual constructor
    return undefined
