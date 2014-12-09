\section{UId}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.UId where

%endif



> import -> DInTmParsersSpecial where
>   (ArgSize, (|DUID (%keyword KwUId%)|)) :
>   (ArgSize, (|DTAG (%keyword KwTag%) ident|)) :
>   (AppSize, (|DTag (%keyword KwTag%) ident (many (sizedDInTm ArgSize))|)) :

> import -> MakeElabRules where
>   makeElab' loc (UID :>: DTAG s) = return $ TAG s :=>: TAG s
