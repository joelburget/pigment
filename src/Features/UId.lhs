\section{UId}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.UId where

%endif



> import -> KeywordConstructors where
>   KwUId  :: Keyword
>   KwTag  :: Keyword

> import -> KeywordTable where
>   key KwUId       = "UId"
>   key KwTag       = "'"

> import -> DInTmParsersSpecial where
>   (ArgSize, (|DUID (%keyword KwUId%)|)) :
>   (ArgSize, (|DTAG (%keyword KwTag%) ident|)) :
>   (AppSize, (|DTag (%keyword KwTag%) ident (many (sizedDInTm ArgSize))|)) :

> import -> DInTmConstructors where
>   DTag :: String -> [DInTm p x] -> DInTm p x

> import -> DInTmPretty where
>   pretty (DTAG s)     = const (kword KwTag <> text s)
>   pretty (DTag s xs)  = wrapDoc (kword KwTag <> text s
>       <+> hsep (map (flip pretty ArgSize) xs)) AppSize

> import -> DInTmTraverse where
>   traverseDTIN f (DTag s xs) = (|(DTag s) (traverse (traverseDTIN f) xs)|)

> import -> MakeElabRules where
>   makeElab' loc (UID :>: DTAG s) = return $ TAG s :=>: TAG s
