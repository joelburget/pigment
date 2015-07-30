{-# LANGUAGE PatternSynonyms #-}
module Tactics.Ornament where

import Control.Applicative
import Control.Error
import Control.Monad.Identity
import Data.Functor.Constant
import Data.Monoid hiding (All)
import Data.Text (Text)
import Data.Traversable

import Kit.BwdFwd
import Kit.MissingLibrary
import Evidences.Tm
import Evidences.Mangler
import Evidences.Eval
import Evidences.Operators
import Evidences.Ornament
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


typeOfDesc :: TyDesc INTM -> INTM
typeOfDesc (ITyDesc (_ :<: ix) args _) = ARR ix (foldr ARR SET (map sndEx args))
typeOfDesc (TyDesc args _) = foldr ARR SET (map sndEx args)


wrapDesc :: TyDesc INTM -> INTM
wrapDesc = C . Ornament


emptyData :: String -> ProofState Name
emptyData name = freshRef (name :<: SET) $ \ref -> do
    nsupply <- askNSupply

    let result :: INTM
        result = TYDESC [] []

    let meta = Metadata False "" False
        ref' = refName ref := DEFN result :<: SET -- XXX get right type
        dev = Dev { devEntries       =  B0
                  , devTip           =  Defined REMPTY (SET :=>: SET)
                  , devNSupply       =  freshNSpace nsupply name
                  , devSuspendState  =  SuspendNone }
    putEntryAbove $ EDEF ref' (mkLastName ref') LETG dev SET emptyMetadata
    return $ refName ref


-- XXX huge TODO:
-- figure out how to handle changes when this thing is in use
addTypeParam :: Text :<: INTM -> ProofState () -- (EXTM :=>: VAL)
addTypeParam param = do
    CDefinition _ ref lastN _ meta <- getCurrentEntry

    let name = refName ref
        DEFN defn :<: _ = refBody ref
        newDesc = case defn of
            TYDESC params cons -> TyDesc (param:params) cons
            ITYDESC i params cons -> ITyDesc i (param:params) cons
        defnTy = typeOfDesc newDesc
        _NEWDESC = wrapDesc newDesc
        newRef = name := DEFN _NEWDESC :<: defnTy

    nsupply <- askNSupply

    putCurrentEntry $ CDefinition LETG newRef lastN defnTy meta
    putDevTip $ Defined _NEWDESC (quote (SET :>: defnTy) nsupply :=>: defnTy)


addConstructor :: Text :<: ConDesc INTM INTM
               -- ^ Name and scheme of constructor to build
               --
               -- TODO(joel) curry?
               -> ProofState ()
addConstructor con = do
    CDefinition _ ref lastN _ meta <- getCurrentEntry

    let name = refName ref
        DEFN defn :<: _ = refBody ref

        -- XXX figure out unindexed story
        newDesc = case defn of
            -- TYDESC params cons -> TyDesc params (con:cons)
            ITYDESC i params cons -> ITyDesc i params (con:cons)
        defnTy = typeOfDesc newDesc
        _NEWDESC = wrapDesc newDesc
        newRef = name := DEFN _NEWDESC :<: defnTy

    nsupply <- askNSupply

    putCurrentEntry $ CDefinition LETG newRef lastN defnTy meta
    putDevTip $ Defined _NEWDESC (quote (SET :>: defnTy) nsupply :=>: defnTy)
