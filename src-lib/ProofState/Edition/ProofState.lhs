<a name="ProofState.Edition.ProofState">The `ProofState` monad</a>
======================

> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes, MultiParamTypeClasses #-}
> module ProofState.Edition.ProofState where

> import qualified Control.Arrow as Arr
> import Control.Applicative
> import Control.Monad.State
> import Data.Functor.Identity

> import Control.Error

> import DisplayLang.Name
> import ProofState.Edition.ProofContext
> import Evidences.Tm

Defining the Proof State monad
------------------------------

The proof state monad provides access to the `ProofContext` as in a
`State` monad, but with the possibility of command failure represented
by `EitherT (StackError e)`.

> type ProofStateT e = StateT ProofContext (Either (StackError e))

Most of the time, we will work in a `ProofStateT` carrying errors
composed with Strings and terms in display syntax. Hence the following
type synonym:

> type ProofState = ProofStateT DInTmRN

Error management toolkit
------------------------

instance ErrorStack (ProofStateT e) VAL where
    throwStack = lift . Left

Some functions, such as `distill`, are defined in the `ProofStateT INTM`
monad. However, Cochon lives in a `ProofStateT DInTmRN` monad.
Therefore, in order to use it, we will need to lift from the former to
the latter.

> mapStackError :: (ErrorTok a -> ErrorTok b) -> StackError a -> StackError b
> mapStackError f = StackError . (fmap . fmap) f . unStackError

> liftError :: (a -> b)
>           -> Either (StackError a) c
>           -> Either (StackError b) c
> liftError f = Arr.left (mapStackError (fmap f))

> liftError' :: (ErrorTok a -> ErrorTok b)
>            -> Either (StackError a) c
>            -> Either (StackError b) c
> liftError' f = Arr.left (mapStackError f)

> throwDInTmRN :: StackError DInTmRN -> ProofState a
> throwDInTmRN = throwStack

> throwDTmStr :: String -> ProofState a
> throwDTmStr = throwDInTmRN . errMsgStack

> liftErrorState :: (a -> b) -> ProofStateT a c -> ProofStateT b c
> liftErrorState f = mapStateT (liftError f)
