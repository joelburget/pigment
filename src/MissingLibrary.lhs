\section{Missing Library}

%if False

> {-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}

> module MissingLibrary where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Error
> import Control.Monad.Identity
> import Control.Monad.State

> import Data.Foldable
> import Data.List
> import Data.Monoid
> import Data.Traversable

%endif

\subsection{Error Handling}

> instance MonadError [String] Maybe where
>   throwError _ = Nothing
>   catchError (Just x)  _ = Just x
>   catchError Nothing   f = f []

> instance Error [String] where
>   strMsg s = [s]


> catchMaybe :: MonadError [e] m => Maybe a -> e -> m a
> catchMaybe (Just x)  _ = return x
> catchMaybe Nothing   s = throwError [s]

> throwError' :: MonadError [e] m => e -> m a
> throwError' e = throwError [e]

> replaceError :: MonadError [e] m => m a -> e -> m a
> replaceError c e = catchError c (\x -> throwError' e)

> replacePMF :: MonadError [String] m => m a -> String -> m a
> replacePMF c s = catchError c f
>   where
>     f (x:xs) =  if "Pattern match failure" `isPrefixOf` x
>                 then throwError' s
>                 else throwError (x:xs)
>     f [] = throwError []

\subsection{Missing Applicatives}

Ah, if only 

< instance Monad m => Applicative m 

were possible. Unfortunately it isn't (at least without |UndecidableInstances|)
so we have to do things the long way...

> instance Error x => Applicative (Either x) where
>   pure = return
>   (<*>) = ap

> instance Applicative (State s) where
>   pure = return
>   (<*>) = ap

> instance Applicative Identity where
>   pure = return
>   (<*>) = ap


\subsection{Missing Instances}

> instance Traversable (Either x) where
>     traverse g (Left a) = pure (Left a)
>     traverse g (Right b) = Right <$> g b

> instance Foldable (Either x) where
>     foldMap = foldMapDefault


\subsection{HalfZip}

> class Functor f => HalfZip f where
>   halfZip :: f x -> f y -> Maybe (f (x,y))







%if False

>   -- HalfZip xs xs = Just (fmap (\x -> (x,x)) xs)

%endif