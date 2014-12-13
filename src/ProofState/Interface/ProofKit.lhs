\section{The |ProofState| Kit}
\label{sec:ProofState.Interface.ProofKit}

%if False

\begin{code}
{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
             GADTs, RankNTypes #-}
module ProofState.Interface.ProofKit where
import Control.Monad.Except
import Kit.BwdFwd
import Kit.MissingLibrary
import NameSupply.NameSupply
import NameSupply.NameSupplier
import ProofState.Edition.ProofContext
import ProofState.Edition.ProofState
import ProofState.Edition.GetSet
import DisplayLang.DisplayTm
import DisplayLang.Name
import Evidences.Tm
import Evidences.TypeChecker
import Evidences.BetaQuotation
\end{code}
%endif


The proof state lives on a rich substrate of operations, inherited
from the |ProofContext| as well as the |ProofState| monad. In this
module, we export these operations as part of the Interface.



\subsection{Accessing the |NameSupply|}


By definition of the |Development| in
Section~\ref{sec:ProofState.Structure.Developments}, we have that
every entry is associated a namespace by the mean of a local name
supply. As a result, the |ProofState| can almost be made a
|NameSupplier|. The exception being that it cannot fork the name
supply, because it cannot generates new namespaces.

\begin{code}
instance NameSupplier (ProofStateT e) where
    freshRef (s :<: ty) f = do
        nsupply <- getDevNSupply
        freshRef (s :<: ty) ( \ref nsupply' -> do
            putDevNSupply nsupply'
            f ref
          ) nsupply
    forkNSupply = error "ProofState does not provide forkNSupply"
    askNSupply = getDevNSupply
\end{code}
We also provide an operator to lift functions from a name supply to
proof state commands.

\begin{code}
withNSupply :: (NameSupply -> x) -> ProofStateT e x
withNSupply f = getDevNSupply >>= return . f
\end{code}
\begin{danger}[Read-only name supply]

Note that this function has no way to return an updated name supply to
the proof context, so it must not leave any references around when it
has finished.

\end{danger}


\subsection{Accessing the type-checker}


First off, we can access the $\beta$-normalizer: the |bquoteHere|
command $\beta$-quotes a term using the local name supply.

\begin{code}
bquoteHere :: Tm {d, VV} REF -> ProofStateT e (Tm {d, TT} REF)
bquoteHere tm = withNSupply $ bquote B0 tm
\end{code}

Secondly, any type-checking problem (defined in the |Check| monad) can
be executed in the |ProofState|.

\begin{code}
runCheckHere :: (ErrorTok e -> ErrorTok DInTmRN) -> Check e a -> ProofState a
runCheckHere f c = do
    me <- withNSupply $ liftError' f . typeCheck c
    lift me
\end{code}
As a consequence, we have |checkHere| to |check| terms against types:

\begin{code}
checkHere :: (TY :>: INTM) -> ProofState (INTM :=>: VAL)
checkHere tt = runCheckHere (fmap DTIN) $ check tt
\end{code}
and |inferHere| to |infer| types from terms:

\begin{code}
inferHere :: EXTM -> ProofState (VAL :<: TY)
inferHere tm = runCheckHere (fmap DTIN) $ infer tm
\end{code}

\subsection{Being paranoiac}


The |validateHere| command performs some sanity checks on the current
location, which may be useful for paranoia purposes.

\begin{code}
validateHere :: ProofState ()
validateHere = do
    m <- getCurrentEntry
    case m of
        CDefinition _ (_ := DEFN tm :<: ty) _ _ _ -> do
            ty' <- bquoteHere ty
            checkHere (SET :>: ty')
                `pushError`  (StackError
                    [ err "validateHere: definition type failed to type-check: SET does not admit"
                    , errTyVal (ty :<: SET)
                    ])
            tm' <- bquoteHere tm
            checkHere (ty :>: tm')
                `pushError`  (StackError
                    [ err "validateHere: definition failed to type-check:"
                    , errTyVal (ty :<: SET)
                    , err "does not admit"
                    , errTyVal (tm :<: ty)
                    ])
            return ()
        CDefinition _ (_ := HOLE _ :<: ty) _ _ _ -> do
            ty' <- bquoteHere ty
            checkHere (SET :>: ty')
                `pushError`  (StackError
                    [ err "validateHere: hole type failed to type-check: SET does not admit"
                    , errTyVal (ty :<: SET)
                    ])
            return ()
        _ -> return ()
\end{code}
