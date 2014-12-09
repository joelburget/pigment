\section{UId}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.UId where

%endif



> import -> MakeElabRules where
>   makeElab' loc (UID :>: DTAG s) = return $ TAG s :=>: TAG s
