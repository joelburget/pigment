<a name="SourceLang.Example">Example</a>
=======

> module SourceLang.Example where

> import Elaboration.ElabMonad
> import SourceLang.Structure
> import SourceLang.Parser
> import SourceLang.Elaborator

> plusC :: Construction Lexed
> plusC = LetConstr
>     (Decl [(Decl [] "x" "Nat"),
>            (Decl [] "y" "Nat")
>           ] "plus" "Nat")
>     (Just (Refinement
>         "plus x y"
>         (ByTac "Nat.Ind x"
>           [
>             Refinement  "plus 'zero y"
>                         (ReturnTac "y")
>                         [],
>             Refinement  "plus ('suc z) y"
>                         ShedTac
>                         []
>           ]
>         )
>         []
>     ))

> parsePlusC :: Construction Parsed
> parsePlusC = case parseConstr plusC of
>     Right c  -> c
>     Left e   -> error e

> elabPlusC :: Elab (Construction Elaborated)
> elabPlusC = elabConstr parsePlusC
