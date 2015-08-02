{-# LANGUAGE PatternSynonyms #-}
-- | Data Type descriptions
--
-- Fundamentally important is the distinction between indexes and parameters.
-- Presentationally, they're mixed -- just like Haskell GADTs, you can specify
-- them in any order and the only distinction between the two is that inexes
-- vary between occurrences, whereas parameters are uniform.
--
-- However, we represent indexes and parameters separately, because each
-- recursive instance of a data type must specify its index.

module Tactics.Ornament where

import Control.Applicative
import Control.Error
import Control.Monad.Identity
import Data.Functor.Constant
import qualified Data.HashMap.Strict as H
import qualified Data.List as L
import Data.Monoid hiding (All)
import Data.Text (Text)
import qualified Data.Text as T
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


unitDesc :: TYDESC
unitDesc = TyDesc
    "unit"
    []
    H.empty
    H.empty
    ["Unit" :<: ConRet H.empty]


pairDesc :: TYDESC
pairDesc = TyDesc
    "pair"
    ["x", "y"]
    H.empty
    (H.fromList [("x", SET), ("y", SET)])
    -- XXX how does binding work?
    ["pair" :<:  ConArg ("fst" :<: (NV 1))
                (ConArg ("snd" :<: (NV 0))
                (ConRet H.empty))
    ]


natDesc :: TYDESC
natDesc = TyDesc
    "nat"
    []
    H.empty
    H.empty
    [ "z" :<: ConRet H.empty
    , "suc" :<: ConRec ("n" :<: H.empty) (ConRet H.empty)
    ]


-- vecDesc :: TYDESC
-- vecDesc = TyDesc
--     ("n" :<: nat)
--     [("a" :<: SET)]
--     [ "nil" :<: ConRet z
--     , "cons" :<: ConArg ("x" :<: NV 0)
--                 (ConRec ("xs" :<: H.singleton "n" n)
--                 (ConRet (H.singleton "n" (suc n))))
--     ]


-- | Find the type of the type constructor.
--
-- For example, @Vect (n : Nat) a@ gives @Nat -> Set -> Set@.
typeOfDesc :: TyDesc INTM -> INTM
typeOfDesc (TyDesc _ ordering indexed nonIndexed _) =
    let allArgs = indexed `H.union` nonIndexed
    in foldr (\name -> ARR (allArgs H.! name)) SET ordering


-- | Convert a data type description to a canonical term
wrapDesc :: TyDesc INTM -> INTM
wrapDesc = C . Ornament


-- | Just to demonstrate how easy it is to detect enumerations
isEnum :: TyDesc t -> Bool
isEnum (TyDesc _ [] _ _ _) = True
isEnum _ = False


-- | Just to demonstrate how easy it is to build an enumeration
enumerate :: Text -> [Text] -> TyDesc t
enumerate name tags =
    let ctors = foldr
            (ConRec . (:<: H.empty))
            (ConRet H.empty)
            tags
    in TyDesc name [] H.empty H.empty [ "tags" :<: ctors ]


emptyData :: Text -> ProofState Name
emptyData name = freshRef (T.unpack name :<: SET) $ \ref -> do
    nsupply <- askNSupply

    let result :: INTM
        result = TYDESC name [] H.empty H.empty []

    let meta = Metadata False "" False
        ref' = refName ref := DEFN result :<: SET -- XXX get right type
        dev = Dev { devEntries       =  B0
                  , devTip           =  Defined REMPTY (SET :=>: SET)
                  , devNSupply       =  freshNSpace nsupply (T.unpack name)
                  , devSuspendState  =  SuspendNone }
    putEntryAbove $ EDEF ref' (mkLastName ref') LETG dev SET emptyMetadata
    return $ refName ref


modifyDesc :: (TYDESC -> TYDESC) -> ProofState ()
modifyDesc f = do
    CDefinition _ ref lastN _ meta <- getCurrentEntry

    let name = refName ref
        DEFN defn :<: _ = refBody ref
        defn' = case defn of
                    C (Ornament d) -> d
                    _ -> error "didn't find type description!"
        newDesc = f defn'
        defnTy = typeOfDesc newDesc
        _NEWDESC = wrapDesc newDesc
        newRef = name := DEFN _NEWDESC :<: defnTy

    nsupply <- askNSupply

    putCurrentEntry $ CDefinition LETG newRef lastN defnTy meta
    putDevTip $ Defined _NEWDESC (quote (SET :>: defnTy) nsupply :=>: defnTy)


-- XXX huge TODO:
-- figure out how to handle changes when this thing is in use
addTypeParam :: Text :<: INTM -> ProofState () -- (EXTM :=>: VAL)
addTypeParam (name :<: param) = modifyDesc $ \(TyDesc n ordering i params cons) ->
    TyDesc n (name:ordering) i (H.insert name param params) cons


-- XXX huge TODO:
-- figure out how to handle changes when this thing is in use
addTypeIndex :: Text :<: INTM -> ProofState () -- (EXTM :=>: VAL)
addTypeIndex (name :<: index) = modifyDesc $ \(TyDesc n ordering i params cons) ->
    TyDesc n (name:ordering) (H.insert name index i) params cons


removeTypeParam :: Text -> ProofState ()
removeTypeParam name = modifyDesc $ \(TyDesc n ordering i params cons) ->
    TyDesc n (L.delete name ordering) i (H.delete name params) cons


removeTypeIndex :: Text -> ProofState ()
removeTypeIndex name = modifyDesc $ \(TyDesc n ordering i params cons) ->
    TyDesc n (L.delete name ordering) (H.delete name i) params cons


addConstructor :: Text :<: ConDesc INTM
               -- ^ Name and scheme of constructor to build
               --
               -- TODO(joel) curry?
               -> ProofState ()
addConstructor con = modifyDesc $ \(TyDesc n ordering i params cons) ->
    TyDesc n ordering i params (con:cons)
