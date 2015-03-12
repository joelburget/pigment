Missing Library
===============

> {-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, TypeFamilies, TypeOperators, UndecidableInstances, TypeSynonymInstances #-}

> module Kit.MissingLibrary where

> import Control.Applicative
> import Control.Newtype
> import Control.Monad.Writer
> import Data.Foldable
> import Data.Functor.Constant
> import Data.Functor.Identity
> import Data.Traversable

Renaming
--------

> trail :: (Applicative f, Foldable t, Monoid (f a)) => t a -> f a
> trail = foldMap pure

> (^$) :: (Traversable f, Applicative i) => (s -> i t) -> f s -> i (f t)
> (^$) = traverse

> iter :: (a -> b -> b) -> [a] -> b -> b
> iter = flip . Prelude.foldr

Missing Instances
-----------------

> instance (Applicative f, Num x, Show (f x), Eq (f x)) => Num (f x) where
>   x + y          = (+) <$> x <*> y
>   x * y          = (*) <$> x <*> y
>   x - y          = (-) <$> x <*> y
>   abs x          = abs <$> x
>   negate x       = negate <$> x
>   signum x       = signum <$> x
>   fromInteger i  = pure $ fromInteger i

Grr.

> instance Monoid (IO ()) where
>   mempty = return ()
>   mappend x y = do x; y

HalfZip
-------

> class Functor f => HalfZip f where
>   halfZip :: f x -> f y -> Maybe (f (x,y))

Functor Kit
-----------

> data (p :*: q)  x = p x :& q x             deriving Show

> instance (Functor p, Functor q) => Functor (p :*: q) where
>   fmap f (px :& qx)  = fmap f px :& fmap f qx

> instance (Traversable p, Traversable q) => Foldable (p :*: q) where
>     foldMap = foldMapDefault

TODO(joel) replace with version from recursion-schemes

> newtype Fix f = InF (f (Fix f))  -- tying the knot

> instance Show (f (Fix f)) => Show (Fix f) where
>   show (InF x) = "InF (" ++ show x ++ ")"

> rec :: Functor f => (f v -> v) -> Fix f -> v
> rec m (InF fd) = m
>     (fmap (rec m {- :: Fix f -> v -})
>           (fd {- :: f (Fix f)-})
>      {- :: f v -})

> instance (Traversable p, Traversable q) => Traversable (p :*: q) where
>   traverse f (px :& qx)  = (:&) <$> traverse f px <*> traverse f qx

> crush :: (Traversable f, Monoid c) => (x -> c) -> f x -> c
> crush m = getConstant . traverse (Constant . m)

> reduce :: (Traversable f, Monoid c) => f c -> c
> reduce = crush id

TODO(joel) - remove this instance, explicitly use Sum

> instance Monoid Int where
>   mempty = 0
>   mappend = (+)

> size :: (Functor f, Traversable f) => Fix f -> Int
> size = rec ((1+) . reduce)

> instance HalfZip Identity where
>   halfZip (Identity x) (Identity y) = pure (Identity (x,y))

> instance (Eq a) => HalfZip (Constant a) where
>   halfZip (Constant x) (Constant y) | x == y = pure (Constant x)
>   halfZip _ _ = Nothing

> instance (HalfZip p, HalfZip q) => HalfZip (p :*: q) where
>   halfZip (x0 :& y0) (x1 :& y1) = (:&) <$> halfZip x0 x1 <*> halfZip y0 y1

>   -- HalfZip xs xs = Just (fmap (\x -> (x,x)) xs)

Newtype Unwrapping
------------------

> instance Newtype (Identity a) a where
>   pack = Identity
>   unpack = runIdentity

Applicative Kit
---------------

The `untilA` operator runs its first argument one or more times until
its second argument succeeds, at which point it returns the result. If
the first argument fails, the whole operation fails. If you have
understood `untilA`, it won't take you long to understand `whileA`.

> untilA :: Alternative f => f () -> f a -> f a
> g `untilA` test = g *> try
>     where try = test <|> (g *> try)

> whileA :: Alternative f => f () -> f a -> f a
> g `whileA` test = try
>     where try = test <|> (g *> try)

The `much` operator runs its argument until it fails, then returns the
state of its last success. It is very similar to `many`, except that it
throws away the results.

> much :: Alternative f => f () -> f ()
> much f = (f *> much f) <|> pure ()

Monadic Kit
-----------

> ignore :: Monad m => m a -> m ()
> ignore f = do
>     f
>     return ()
