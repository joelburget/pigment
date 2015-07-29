{-# LANGUAGE ScopedTypeVariables, GADTs, FlexibleInstances, TypeOperators,
    TypeSynonymInstances, OverloadedStrings, PatternSynonyms,
    LiberalTypeSynonyms, FlexibleContexts, RebindableSyntax,
    MultiParamTypeClasses #-}

module Cochon.Reactify where

import Prelude hiding ((>>), return)

import qualified Data.Aeson as Aeson
import qualified Data.Foldable as Foldable
import Data.Functor.Identity
import Data.HashMap.Strict as H
import Data.List
import Data.Monoid ((<>), mempty, mconcat)
import Data.String (fromString)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void

import Cochon.Imports
import Cochon.Model
import ProofState.Structure.Developments
import Distillation.Distiller
import Distillation.Scheme
import DisplayLang.DisplayTm
import DisplayLang.Name
import DisplayLang.Scheme
import Evidences.Tm
import Kit.BwdFwd
import Kit.MissingLibrary hiding ((<>))
import ProofState.Edition.ProofState

import React hiding (key)
import React.Rebindable


forReact :: Foldable.Foldable f => f a -> (a -> ReactNode b) -> ReactNode b
forReact = flip Foldable.foldMap


can_ :: Can DInTmRN -> ReactNode TermTransition
can_ = classLeaf $ dumbClass
    { React.name = "Can"
    , renderFn = \props _ ->
        let (tag, children) = canReactify props
        in canLayout_ tag children
    }

canReactify :: Can DInTmRN -> (Text, ReactNode TermTransition)
canReactify Set       = ("set", mempty)
canReactify (Pi s t)  = ("pi", pi_ (DPI s t))
canReactify (Con x)   = ("con", dInTmRN_ x)

-- Definitional Equality

canReactify (EqBlue pp qq) = ("eqblue", dInTmRN_ (DEqBlue (foo pp) (foo qq)))
  where
    foo :: (DInTmRN :>: DInTmRN) -> DExTmRN
    foo (_    :>: DN x  ) = x
    foo (xty  :>: x     ) = DType xty ::$ [A x]

-- Labelled Types

canReactify (Label l t) = ("label", dInTmRN_ l <> dInTmRN_ t)
canReactify (LRet x) = ("lret", dInTmRN_ x)

-- XXX Prob?

-- Prop

canReactify Prop           = ("prop", mempty)
canReactify (Prf p)        = ("prf", dInTmRN_ p)
canReactify Trivial        = ("trivial", mempty)
canReactify Absurd         = ("absurd", mempty)
canReactify (And p q)      = ("and", dInTmRN_ p <> dInTmRN_ q)
canReactify (All p q)      = ("all", all_ (DALL p q))
canReactify (Box (Irr p))  = ("box", dInTmRN_ p)
canReactify (Inh ty)       = ("inh", dInTmRN_ ty)
canReactify (Wit t)        = ("wit", dInTmRN_ t)

-- Quotients
-- x : Set
-- r - relation
-- p - proof of equivalence relation
canReactify (Quotient x r p) = ("quotient", forReact [x, r, p] dInTmRN_)
    -- reactify x
    -- " // "
    -- reactify r
    -- " ("
    -- reactify p
    -- ")"

canReactify RSig              = ("rsig", mempty)
canReactify REmpty            = ("rempty", mempty)
canReactify (RCons s i t)     = ("rcons", forReact [s, i, t] dInTmRN_)
    -- reactify s
    -- ">"
    -- reactify i
    -- " , "
    -- reactify t
-- XXX Record?

-- Sigma

canReactify Unit         = ("unit", mempty)
canReactify Void         = ("void", mempty)
canReactify (Sigma s t)  = ("sigma", sigma_ (DSIGMA s t))
canReactify (Pair a b)   = ("pair", pair_ (DPAIR a b))

-- UId

canReactify UId      = ("uid", mempty)
canReactify (Tag s)  = ("tag", fromString s)

-- canReactify can       = fromString $ "TODO(joel) - " ++ show can

pi_ :: DInTmRN -> ReactNode TermTransition
pi_ p@(DPI s t) = piLayout_ (mconcat (piHelper p))


piHelper :: DInTmRN -> [ReactNode TermTransition]
-- IE `s -> t`
piHelper (DPI s (DL (DK t))) = dInTmRN_ s : piHelper t
-- IE `(x : s) -> t`
piHelper (DPI s (DL (x ::. t))) =
    dependentParamLayout_ (T.pack x) (dInTmRN_ s) : piHelper t
-- IE `pi s t`
piHelper (DPI s t) = [justPiLayout_ (dInTmRN_ s) (dInTmRN_ t)]
-- IE `tm`
piHelper tm = [dInTmRN_ tm]


dscope_ :: DSCOPE -> ReactNode TermTransition
dscope_ = classLeaf $ dumbClass
    { React.name = "DSCOPE"
    , renderFn = \s _ ->
        let (bindings, result) = lambdaAccum (B0 :< dScopeName s) (dScopeTm s)
            bindings' = forReact bindings fromString
            result' = dInTmRN_ result
        in dscopeLayout_ (bindings' <> result')
    }

lambdaAccum :: Bwd String -> DInTmRN -> (Bwd String, DInTmRN)
lambdaAccum vs (DL s) = lambdaAccum (vs :< dScopeName s) (dScopeTm s)
lambdaAccum vs tm = (vs, tm)


dInTmRN_ :: DInTmRN -> ReactNode TermTransition
dInTmRN_ = classLeaf $ dumbClass
    { React.name = "DInTmRN"
    , renderFn = \tm _ ->
        let (tag, details) = case tm of
                DL s -> ("dl", dscope_ s)
                (DC c) -> ("dc", can_ c)
                (DN n) -> ("dn", dExTmRN_ n)
                (DQ x) -> ("dq", fromString x)
                DU     -> ("du", mempty)
                (DT (InTmWrap tm)) -> ("dt", "TODO DT")
                (DEqBlue t u) -> ("deqblue", dExTmRN_ t <> dExTmRN_ u)
                (DIMu (Just s   :?=: _) _) -> ("dimujust", dInTmRN_ s)
                (DIMu (Nothing  :?=: (Identity ii :& Identity d)) i) ->
                    ("dimunothing", forReact [ii, d, i] dInTmRN_)
                (DAnchor name _) -> ("danchor", fromString name)
                (DTAG name) -> ("dtag1", fromString name)
                (DTag name tms) ->
                    ("dtag2", fromString name <> forReact tms dInTmRN_)
        in dInTmRNLayout_ tag details
    }


dExTmRN_ :: DExTmRN -> ReactNode TermTransition
dExTmRN_ = classLeaf $ dumbClass
    { React.name = "DExTmRN"
    , renderFn = \(n ::$ els) _ -> dExTmRNLayout_ $ do
        dhead_ n
        dspine_ els
    }


dspine_ :: DSPINE -> ReactNode TermTransition
dspine_ = classLeaf $ dumbClass
    { React.name = "DSpine"
    , renderFn = \els _ -> dspineLayout_ (forReact els elim_)
    }


relname_ :: RelName -> ReactNode TermTransition
relname_ name = relnameLayout_ (forReact name relnamePiece_)

relnamePiece_ :: (String, Offs) -> ReactNode TermTransition
relnamePiece_ (str, offs) =
    let (tag, n) = case offs of
            Rel n -> ("rel", T.pack (show n))
            Abs n -> ("abs", T.pack (show n))
    in relnamePieceLayout_ tag n (T.pack str)


dhead_ :: DHEAD -> ReactNode TermTransition
dhead_ = classLeaf $ dumbClass
    { React.name = "DHEAD"
    , renderFn = \dhead _ ->
        let (tag, children) = case dhead of
                DP x -> ("param", relname_ x)
                DType ty -> ("annotation", dInTmRN_ ty)
                DTEx (ExTmWrap ex) -> ("embedding", "TODO DTEx")
        in dheadLayout_ tag children
    }

scheme_ :: Scheme DInTmRN -> ReactNode TermTransition
scheme_ = classLeaf $ dumbClass
    { React.name = "Scheme"
    , renderFn = \scheme _ ->
        let (tag, children) = case scheme of
                SchType ty -> ("type", dInTmRN_ ty)
                SchExplicitPi (name :<: from) to ->
                    ("explicit", do
                        fromString name
                        scheme_ from
                        scheme_ to
                    )
                SchImplicitPi (name :<: from) to ->
                    ("implicit", do
                        fromString name
                        dInTmRN_ from
                        scheme_ to
                    )
        in schemeLayout_ tag children
    }

  -- reactifyEnumIndex :: Int -> DInTmRN -> Pure React'
  -- reactifyEnumIndex n DZE      = fromString $ show n
  -- reactifyEnumIndex n (DSU t)  = reactifyEnumIndex (succ n) t
  -- reactifyEnumIndex n tm       = do
  --     fromString (show n)
  --     reactKword KwPlus
  --     reactify tm


-- build up a list of inputs
-- allHelper :: DInTmRN -> []
-- allHelper (DALL (DPRF p) (DLK q)) = Implies p q
-- allHelper (DALL s (DL x ::. t)) = Implies (x : s) (allHelper t)
-- allHelper (DALL s (DLK t)) = allHelper (DALL s (DL ("_" ::. t)))
-- allHelper (DALL s t) = All s t
-- allHelper tm = reactify tm
--
-- allLayout_ ::

all_ :: DInTmRN -> ReactNode TermTransition
all_ = classLeaf $ dumbClass
    { React.name = "All"
    , renderFn = \props _ -> "TODO all_" -- allLayout_ (allHelper props)
    }

pair_ :: DInTmRN -> ReactNode TermTransition
pair_ = classLeaf $ dumbClass
    { React.name = "Pair"
    , renderFn = \props _ -> pairLayout_ (forReact (pairHelper props) dInTmRN_)
    }

-- TODO - as written this always requires a terminating DVOID
pairHelper :: DInTmRN -> [DInTmRN]
pairHelper DVOID = []
pairHelper (DPAIR a b) = a : pairHelper b


{-
sigma_ :: ReactNode TermTransition -> DInTmRN -> ReactNode TermTransition
sigma_ d DUNIT                      = reactifySigmaDone d ""
sigma_ d (DSIGMA s (DL (x ::. t)))  = reactifySigma
    (d >> fromString x >> reactKword KwAsc >> reactify s >> reactKword KwSemi)
    t
sigma_ d (DSIGMA s (DL (DK t)))     = reactifySigma
    (d >> reactify s >> reactKword KwSemi) t
sigma_ d (DSIGMA s t) = reactifySigmaDone d
    (reactKword KwSig >> reactify s >> reactify t)
sigma_ d t = reactifySigmaDone d (reactify t)

reactifySigmaDone :: ReactNode TermTransition -> ReactNode TermTransition -> ReactNode TermTransition
reactifySigmaDone s t = div_ [ class_ "sigma-done" ] $
    reactKword KwSig >> reactBrackets Round (s >> t)
-}

sigma_ :: DInTmRN -> ReactNode TermTransition
sigma_ = classLeaf $ dumbClass
    { React.name = "Sigma"
    , renderFn = \sigma _ ->
        let (tag, children) = case sigma of
                DUNIT -> ("dunit", mempty)

                -- lambda with binding
                DSIGMA s (DL (x ::. t)) ->
                    ("bind", dInTmRN_ s <> fromString x <> dInTmRN_ t)

                -- lambda with a constant
                DSIGMA s (DL (DK t)) -> ("const", dInTmRN_ s <> dInTmRN_ t)

                -- something else? what could this be?
                DSIGMA s t -> ("other", dInTmRN_ s <> dInTmRN_ t)
        in sigmaLayout_ tag children
    }

-- The `Elim` functor is straightforward.

elimLayout_ :: (Text, Maybe (ReactNode TermTransition)) -> ReactNode TermTransition
elimLayout_ = undefined

elim_ :: Elim DInTmRN -> ReactNode TermTransition
elim_ = classLeaf $ dumbClass
    { React.name = "Elim"
    , renderFn = \elim _ -> elimLayout_ $ case elim of
        A t -> ("a", Just (dInTmRN_ t))
        Out -> ("out", Nothing)
        Call t -> ("call", Just (dInTmRN_ t))
        Fst -> ("fst", Nothing)
        Snd -> ("snd", Nothing)
    }
