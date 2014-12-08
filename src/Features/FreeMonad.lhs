\section{FreeMonad}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.FreeMonad where

%endif



> import -> OpCompile where
>   ("substMonad", [d, x, y, f, t]) -> App (Var "__substMonad") [d, f, t]
>   ("elimMonad", [d, x, v, p, mc, mv]) -> App (Var "__elimMonad") [d, mv, mc, v]

\question{What should the coercion rule be for |COMPOSITE|?}

> import -> Coerce where
>   coerce (Monad (d1, d2) (x1, x2)) q (RETURN v) =
>     Right . RETURN $ coe @@ [x1, x2, CON (q $$ Snd), v]
>   coerce (Monad (d1, d2) (x1, x2)) q (COMPOSITE y) =
>     Right . COMPOSITE $ coe @@ [
>         descOp @@ [d1, MONAD d1 x1],
>         descOp @@ [d2, MONAD d2 x2],
>         error "FreeMonad.coerce: missing equality proof",
>         y
>       ]


> import -> KeywordConstructors where
>   KwMonad   :: Keyword
>   KwReturn  :: Keyword

> import -> KeywordTable where
>   key KwMonad     = "Monad"
>   key KwReturn    = "`"  -- rename me

> import -> DInTmParsersSpecial where
>   (ArgSize, (|DRETURN (%keyword KwReturn%) (sizedDInTm ArgSize)|)) :
>   (AndSize, (|DMONAD (%keyword KwMonad%) (sizedDInTm ArgSize) (sizedDInTm ArgSize)|)) :
