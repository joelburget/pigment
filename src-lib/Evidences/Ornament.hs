module Evidences.Ornament where

import Data.Text (Text)

import {-# SOURCE #-} Evidences.Tm


-- | Constructor descriptions
--
-- Condesc i t -- Constructor description with index type i and term type t.
--
-- TODO add annotations
data ConDesc :: * -> * -> * where
    -- Take an argument and continue with the description
    ConArg :: (Text :<: t) -> ConDesc i t -> ConDesc i t

    -- Return at this index
    ConRet :: i -> ConDesc i t

    -- Recursively take at this index
    ConRec :: (Text :<: i) -> ConDesc i t -> ConDesc i t

    deriving (Show, Eq)


data TyDesc :: * -> * where
    -- | Indexed type description
    ITyDesc :: Text :<: t
           -- ^ the index type
           --
           -- TODO(joel) - more than one?
           -- TODO(joel) - how do indexed and non-indexed arguments interact?
           -> [Text :<: t]
           -- ^ the non-index arguments
           --
           -- TODO(joel) - Is it possible for these arguments to telescope?
           -- IE can typeOfDesc be a pi type?
           -> [Text :<: ConDesc t t]
           -- ^ the constructors
           -> TyDesc t

    -- | Non-indexed type description
    TyDesc :: [Text :<: t]
           -- ^ the non-index arguments
           -> [Text :<: ConDesc () t]
           -- ^ the constructors
           -> TyDesc t

    deriving (Show, Eq)
