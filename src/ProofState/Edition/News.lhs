\section{News about updated references}
\label{sec:ProofState.Edition.News}

%if False

\begin{code}
{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE FlexibleInstances, TypeOperators, GADTs #-}
module ProofState.Edition.News where
import Control.Monad.Writer
import Data.Traversable
import Data.Foldable hiding (foldr)
import Data.Maybe
import Evidences.Tm
import Evidences.Eval
\end{code}
%endif


The news system represents stored updates to references. For
performance reasons, we do not wish to traverse the entire proof state
every time modifications are made to one part of the tree. Instead, we
store news entries below the cursor, and update following entries when
the cursor moves down. This section describes the data that is stored
in the proof state, and section \ref{sec:Elaboration.Wire} describes
how news is propagated.


\subsection{News}


|News| represents possible changes to references. At the moment, it may
be |GoodNews| (the reference has become more defined) or |NoNews|
(even better from our perspective, as the reference has not
changed). Note that |News| is ordered by increasing ``niceness''.

When we come to implement functionality to remove definitions from the proof state,
we will also need |BadNews| (the reference has changed but is not more informative)
and |DeletedNews| (the reference has gone completely).

\begin{code}
data News = DeletedNews | BadNews | GoodNews | NoNews deriving (Eq, Ord, Show)
\end{code}
Handily, |News| is a monoid where the neutral element is |NoNews| and composing
two |News| takes the less nice.

\begin{code}
instance Monoid News where
    mempty   = NoNews
    mappend  = min
\end{code}

\subsection{News Bulletin}

A |NewsBulletin| is a list of pairs of updated references and the news about them.

\begin{code}
type NewsBulletin = [(REF, News)]
\end{code}

\subsubsection{Adding news}

The |addNews| function adds the given news to the bulletin, if it is newsworthy.

\begin{code}
addNews :: (REF, News) -> NewsBulletin ->  NewsBulletin
addNews (_,  NoNews)  old  = old
addNews (r,  n)       old  = (r, n `mappend` n') : old' where
  -- Find previous versions n' (if any), 
  -- Remove duplicate in old':
  (n', old') = seek old
  seek [] = (NoNews, [])
  seek ((r', n') : old) | r == r' = (n', old)
  seek (rn : old) = (n', rn : old') where (n', old') = seek old
\end{code}
Using |seek|, we enforce the invariant that any reference
appears at most once in a |NewsBulletin|.


\subsubsection{Getting the latest news}

The |lookupNews| function returns the news about a reference contained
in the bulletin, which may be |NoNews| if the reference is not
present.

\begin{code}
lookupNews :: NewsBulletin -> REF -> News
lookupNews nb ref = fromMaybe NoNews (lookup ref nb)
\end{code}

The |getNews| function looks for a reference in the news bulletin,
and returns it with its news if it is found, or returns |Nothing| if
not.

\begin{code}
getNews :: NewsBulletin -> REF -> Maybe (REF, News)
getNews nb ref = find ((== ref) . fst) nb
\end{code}

The |getLatest| function returns the most up-to-date copy of the given
reference, either the one from the bulletin if it is present, or the
one passed in otherwise. If given a |FAKE| reference, it will always
return one, regardless of the status of the reference in the bulletin.
This ensures that fake references in labels have their types updated
without turning into real definitions unexpectedly.

\begin{code}
getLatest :: NewsBulletin -> REF -> REF
getLatest news ref@(nom := FAKE :<: _) = nom := FAKE :<: ty
    where _ := _ :<: ty = realGetLatest news ref
getLatest news ref = realGetLatest news ref
\end{code}
This is implemented via |realGetLatest|, which ignores fakery. The slightly odd
recursive case arises because equality for references just compares their names.

\begin{code}
realGetLatest :: NewsBulletin -> REF -> REF
realGetLatest []                ref = ref
realGetLatest ((ref', _):news)  ref
    | ref == ref'  = ref'
    | otherwise    = getLatest news ref
\end{code}


\subsubsection{Merging news}


The |mergeNews| function takes older and newer bulletins, and composes them to
produce a single bulletin with the worst news about every reference mentioned
in either.

\begin{code}
mergeNews :: NewsBulletin -> NewsBulletin -> NewsBulletin
mergeNews new [] = new
mergeNews new old = foldr addNews old new
\end{code}

\subsubsection{Read all about it}

The |tellNews| function applies a bulletin to a term. It returns the updated
term and the news about it (i.e.\ the least nice news of any reference used
in the term). Using the |Writer| monad allows the term to be updated and the
news about it calculated in a single traversal. Note that we ensure |FAKE|
references remain as they are, as in |getLatest|.

\begin{code}
tellNews :: NewsBulletin -> Tm {d, TT} REF -> (Tm {d, TT} REF, News)
tellNews []    tm = (tm, NoNews)
tellNews news  tm = runWriter $ traverse teller tm
  where
    teller :: REF -> Writer News REF
    teller r = case getNews news r of
        Nothing -> return r
        Just (r', n) -> tell n >> return (fixFake r r')
    fixFake :: REF -> REF -> REF
    fixFake (_ := FAKE :<: _)  (n := _ :<: ty)  = n := FAKE :<: ty
    fixFake _                  r                = r
\end{code}
The |tellNewsEval| function takes a bulletin, term and its present value.
It updates the term with the bulletin and re-evaluates it if necessary.

\begin{code}
tellNewsEval :: NewsBulletin -> INTM :=>: VAL -> (INTM :=>: VAL, News)
tellNewsEval news (tm :=>: tv) = case tellNews news tm of
    (_,    NoNews)    -> (tm   :=>: tv,        NoNews)
    (tm',  GoodNews)  -> (tm'  :=>: evTm tm',  GoodNews)
\end{code}
