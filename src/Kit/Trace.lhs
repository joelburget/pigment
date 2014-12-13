\section{Trace}

%if False

\begin{code}
{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module Kit.Trace where
import Debug.Trace
\end{code}
%endif

Let us enumerate the different flavours of tracing available:

\begin{code}
data Trace =  ProofTrace 
           |  SimpTrace 
           |  ElimTrace 
           |  SchedTrace
           |  ElabTrace
              deriving Show
\end{code}
We then can switch each one on or off individually:

\begin{code}
traceEnabled :: Trace -> Bool
traceEnabled ProofTrace  = True
traceEnabled SimpTrace   = False
traceEnabled ElimTrace   = False
traceEnabled SchedTrace  = False
traceEnabled ElabTrace   = True
\end{code}
That's fairly trivial, yet I'm pretty sure this goddamn laziness won't
skip some traces (ML programmer speaking here).

\begin{code}
monadTrace :: Monad m => Trace -> String -> m ()
monadTrace t s  | traceEnabled t  = do
    () <- trace  ("[" ++ show t ++ "] " ++ s) $ return ()
    return ()
                | otherwise       = return ()
\end{code}
Some handy aliases for the tracing function:

\begin{code}
proofTrace  = monadTrace ProofTrace
simpTrace   = monadTrace SimpTrace
elimTrace   = monadTrace ElimTrace
schedTrace  = monadTrace SchedTrace
elabTrace   = monadTrace ElabTrace\end{code}
