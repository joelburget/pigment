module Evidences.Ornament where

import Data.Text (Text)
import qualified Data.HashMap.Strict as H

import {-# SOURCE #-} Evidences.Tm


-- | Constructor descriptions
--
-- Condesc t -- Constructor description with term type t.
--
-- TODO add annotations
data ConDesc t
    -- | Take an argument and continue with the description
    = ConArg (Text :<: t) (ConDesc t)

    -- | Return at this index
    | ConRet (Index t)

    -- | Recursively take at this index
    --
    -- XXX This binds the name!
    -- TODO figure out a good explanation for this binding thing. Like, why
    -- can't you bind right-to-left?
    | ConRec (Text :<: Index t) (ConDesc t)

    deriving (Show, Eq)


type Index t = H.HashMap Text t


data TyDesc :: * -> * where
    -- | Indexed type description
    TyDesc :: Text
           -- ^ What's it called?
           -> [Text]
           -- ^ Argument ordering
           -> H.HashMap Text t
           -- ^ indexed arguments
           --
           -> H.HashMap Text t
           -- ^ the non-index arguments
           --
           -- TODO(joel) - Is it possible for these arguments to telescope?
           -- IE can typeOfDesc be a pi type?
           -> [Text :<: ConDesc t]
           -- ^ the constructors
           -> TyDesc t

    deriving (Show, Eq)
