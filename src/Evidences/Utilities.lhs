\section{Utilities}

%if False

\begin{code}
{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
    TypeSynonymInstances, FlexibleInstances, FlexibleContexts,
    ScopedTypeVariables #-}
module Evidences.Utilities where
import Prelude hiding (elem)
import Data.Foldable
import NameSupply.NameSupplier
import Evidences.Tm
import Evidences.Mangler
import Evidences.BetaQuotation
import Evidences.Eval
import Kit.BwdFwd
\end{code}
%endif

\subsection{From |EXTM| to |INTM| and back again}

Various commands yield an |EXTM :=>: VAL|, and we sometimes need to
convert this to an |INTM :=>: VAL|.

\begin{code}
neutralise :: Monad m => (EXTM :=>: VAL) -> m (INTM :=>: VAL)
neutralise (n :=>: v) = return $ N n :=>: v
\end{code}
Conversely, sometimes we have an |INTM| and the value representation of its
type, but need an |EXTM|. We avoid |bquote| if possible.

\begin{code}
annotate :: NameSupplier m => INTM -> TY -> m EXTM
annotate (N n)  _   = return n
annotate t      ty  = bquote B0 ty >>= return . (t :?)
\end{code}

\subsection{Discharging a list of hypotheses over a term}

The |dischargeLam| function discharges and $\lambda$-binds a list of references
over a term.

\begin{code}
dischargeLam :: Bwd REF -> INTM -> INTM
dischargeLam bs v = wrapLambdas bs (bs -|| v)
  where
    wrapLambdas :: Bwd REF -> INTM -> INTM
    wrapLambdas B0 tm = tm
    wrapLambdas (bs :< (n := _)) tm = wrapLambdas bs (L (fst (last n) :. tm))
\end{code}
The |dischargeF| function discharges and binds a list of typed references over a
term, using the given |binder| function at each step. The |binder| takes a |Bool|
indicating whether the corresponding reference occurred in the original term, the
name advice for the binder, the type of the reference and the term to be bound.

\begin{code}
dischargeF ::  (Bool -> String -> INTM -> INTM -> INTM) ->
                        Bwd (REF :<: INTM) -> INTM -> INTM
dischargeF binder bs v =
    wrapFs bs (fmap (v `contains`) bs') (bs' -|| v)
  where
    bs' = fmap fstEx bs
    contains :: INTM -> REF -> Bool
    contains = flip elem
    wrapFs :: Bwd (REF :<: INTM) -> Bwd Bool -> INTM -> INTM
    wrapFs B0 B0 tm = tm
    wrapFs (bs :< ((n := _) :<: ty)) (cs :< c) tm =
        wrapFs bs cs (binder c (fst (last n)) ty tm)
\end{code}
Using the above, we can easily discharge and $\forall$-bind or discharge and
$\Pi$-bind. Note that when the bound variable is not used, a |K| binder is used.
For |dischargeAll|, the initial term must be in the form |PRF q| for some
proposition |q|. 

\begin{code}
dischargeAll :: Bwd (REF :<: INTM) -> INTM -> INTM
dischargeAll = dischargeF f
  where 
    f :: Bool -> String -> INTM -> INTM -> INTM
    f False  x (PRF p)  (PRF q) = PRF (IMP p q)
    f _      x s        (PRF q) = PRF (ALLV x s q)
dischargePi :: Bwd (REF :<: INTM) -> INTM -> INTM
dischargePi = dischargeF f
  where
    f :: Bool -> String -> INTM -> INTM -> INTM
    f _   x p q = PIV x p q
\end{code}

The |dischargeAllREF| function calls |dischargeAll| on the type of a reference,
producing a reference with the same name but whose type is $\forall$-abstracted
over the list of references. This should be used with caution, as it could lead
to having two references with the same name but different types.

\begin{code}
dischargeAllREF :: Bwd (REF :<: INTM) -> REF :<: INTM -> REF :<: INTM
dischargeAllREF bs ((n := DECL :<: _) :<: ty) =
    (n := DECL :<: evTm ty') :<: ty'
  where ty' = dischargeAll bs ty
\end{code}
The |mkFun| function turns a Haskell function into a term by applying it to a
fresh reference and discharging over that reference.

\begin{code}
mkFun :: NameSupplier m => (REF -> INTM) -> m INTM
mkFun f = freshRef ("fy" :<: error "mkFun: reference type undefined") $
    \ ref -> return $ dischargeLam (B0 :< ref) (f ref)
\end{code}

\subsection{Term construction and deconstruction}

The |splitSpine| function takes a neutral value and tries to split it into a
reference and a spine of arguments to which it is applied.
\adam{where should this live?}

\begin{code}
splitSpine :: NEU -> Maybe (REF, [VAL])
splitSpine (P r) = return (r, [])
splitSpine (n :$ A a) = do
    (r, as) <- splitSpine n
    return (r, as ++ [a])
splitSpine _ = Nothing\end{code}
