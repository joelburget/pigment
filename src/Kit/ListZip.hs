{-# LANGUAGE DeriveGeneric #-}
module Kit.ListZip where

import Data.Foldable
import Data.Monoid
import GHC.Generics

import GHCJS.Marshal

import Kit.BwdFwd

data ListZip a = ListZip
    { later  :: Bwd a
    , focus  :: a
    , earlier :: Fwd a
    } deriving Generic

instance FromJSRef a => FromJSRef (ListZip a) where

listZipFromFwd :: Fwd a -> Maybe (ListZip a)
listZipFromFwd (a :> as) = Just (ListZip B0 a as)
listZipFromFwd _  = Nothing

listZipFromList :: [a] -> Maybe (ListZip a)
listZipFromList = listZipFromFwd . fwdList

moveEarlier :: ListZip a -> Maybe (ListZip a)
moveEarlier (ListZip late a (a' :> early)) =
    Just (ListZip (late :< a) a' early)
moveEarlier _ = Nothing

moveLater :: ListZip a -> Maybe (ListZip a)
moveLater (ListZip (late :< a') a early) =
    Just (ListZip late a' (a :> early))
moveLater _ = Nothing

instance Functor ListZip where
    fmap f (ListZip late focus early) =
        ListZip (fmap f late) (f focus) (fmap f early)

instance Foldable ListZip where
    foldMap f (ListZip late focus early) =
        foldMap f late <> f focus <> foldMap f early
