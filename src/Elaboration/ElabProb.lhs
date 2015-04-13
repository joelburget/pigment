<a name="Elaboration.ElabProb">`ElabProb`: syntactic representation of elaboration problems</a>
============================================================

> {-# LANGUAGE GADTs, TypeOperators, TypeSynonymInstances, FlexibleInstances,
>              MultiParamTypeClasses, GeneralizedNewtypeDeriving,
>              PatternGuards #-}
> module Elaboration.ElabProb where
> import Control.Applicative
> import Data.Foldable
> import Data.Traversable
> import Evidences.Tm
> import Evidences.Eval
> import DisplayLang.DisplayTm
> import DisplayLang.Name

An `ElabProb` is a syntactic representation of an elaboration problem.
Examples include elaborating a particular piece of display syntax into
an evidence term and waiting for something to happen before elaboration
can proceed. Crucially, an elaboration problem can be suspended by
storing it in the proof state. This allows it to be left alone until
more progress can be made (e.g. because it has been updated with news,
or because the scheduler is free to make some non-local change to the
proof state).

It caches the value representations of terms it contains.

> data ElabProb x
>     =  ElabDone (InTm x :=>: Maybe VAL)
>        -- ^ succeed with given term
>     |  ElabHope
>        -- ^ hope for a solution to turn up
>     |  ElabProb (DInTm x RelName)
>        -- ^ elaborate `In` display term
>     |  ElabInferProb (DExTm x RelName)
>        -- ^ elaborate and infer type of `Ex` display term
>     |  WaitCan (InTm x :=>: Maybe VAL) (ElabProb x)
>        -- ^ wait for value to become canonical
>     |  WaitSolve x (InTm x :=>: Maybe VAL) (ElabProb x)
>        -- ^ wait for reference to be solved with term
>     |  ElabSchedule (ElabProb x)
>        -- ^ kick off the scheduler

`ElabProb` is a traversable functor, parameterised by the type of
references, which are typically `REF`s. Note that traversal will discard
the cached values, but this is okay because the terms need to be
re-evaluated after they have been updated anyway.

> type EProb = ElabProb REF

An elaboration problem is said to be *unstable* if the scheduler can
make progress on it, and *stable* if not. At present, the only kind of
stable elaboration problem is waiting for a non-canonical term to become
canonical.

> isUnstable :: EProb -> Bool
> isUnstable (ElabDone _)                                    = True
> isUnstable ElabHope                                        = True
> isUnstable (ElabProb _)                                    = True
> isUnstable (ElabInferProb _)                               = True
> isUnstable (WaitCan (_ :=>: Just (C _)) _)                 = True
> isUnstable (WaitCan (tm :=>: Nothing) _) | C _ <- evTm tm  = True
> isUnstable (WaitCan _ _)                                   = False
> isUnstable (WaitSolve _ _ _)                               = True
> isUnstable (ElabSchedule _)                                = True

Since `ElabProb` caches value representations of its terms, we define
some handy functions for producing and manipulating these.

> justEval :: INTM :=>: VAL -> INTM :=>: Maybe VAL
> justEval (tm :=>: v) = tm :=>: Just v
> maybeEval :: INTM :=>: Maybe VAL -> INTM :=>: VAL
> maybeEval (tm :=>: Just v)   =  tm :=>:  v
> maybeEval (tm :=>: Nothing)  =  tm :=>:  evTm tm

> instance Show a => Show (ElabProb a) where
>     show (ElabDone tt)            = "ElabDone (" ++ show tt ++ ")"
>     show ElabHope                 = "ElabHope"
>     show (ElabProb tm)            = "ElabProb (" ++ show tm ++ ")"
>     show (ElabInferProb tm)       = "ElabInferProb (" ++ show tm ++ ")"
>     show (WaitCan tt prob)        = "WaitCan (" ++ show tt ++ ") ("
>                                         ++ show prob ++ ")"
>     show (WaitSolve ref tt prob)  = "WaitSolve (" ++ show ref ++ ") ("
>                                         ++ show tt ++ ") (" ++ show prob ++ ")"
>     show (ElabSchedule prob)      = "ElabSchedule (" ++ show prob ++ ")"

> instance Functor ElabProb where
>     fmap = fmapDefault

> instance Foldable ElabProb where
>     foldMap = foldMapDefault

> instance Traversable ElabProb where
>     traverse f (ElabDone tt)            = ElabDone <$> travEval f tt
>     traverse f ElabHope                 = pure ElabHope
>     traverse f (ElabProb tm)            = ElabProb <$> traverseDTIN f tm
>     traverse f (ElabInferProb tm)       = ElabInferProb <$> traverseDTEX f tm
>     traverse f (WaitCan tt prob)        = WaitCan <$> travEval f tt <*> traverse f prob
>     traverse f (WaitSolve ref tt prob)  = WaitSolve <$> f ref <*> travEval f tt <*> traverse f prob
>     traverse f (ElabSchedule prob)      = ElabSchedule <$> traverse f prob
> travEval :: Applicative f => (p -> f q) -> InTm p :=>: Maybe VAL -> f (InTm q :=>: Maybe VAL)
> travEval f (tm :=>: _) = (:=>:) <$> traverse f tm <*> pure Nothing
