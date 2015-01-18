Loading Developments
====================

> {-# LANGUAGE TypeOperators #-}

> module Cochon.DevLoad () where

> import Control.Monad.State
> import Control.Monad.Except
> import Control.Applicative

> import Kit.BwdFwd
> import Kit.Parsley
> import Cochon.Cochon
> import Cochon.Error
> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.Lexer
> import DisplayLang.TmParse
> import DisplayLang.PrettyPrint
> import ProofState.Structure.Developments
> import ProofState.Edition.ProofContext
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation
> import ProofState.Interface.Module
> import Elaboration.Elaborator
> import NameSupply.NameSupply
> import NameSupply.NameSupplier
> import Evidences.Tm

Parsing a Development
---------------------

To parse a development, we represent it as a list of `DevLine`s, each of
which corresponds to a `Parameter` or `Definition` entry and stores
enough information to reconstruct it. Note that at this stage, we simply
tag each definition with a list of commands to execute later.

> data DevLine
>   =  DLParam ParamKind String DInTmRN
>   |  DLDef String [DevLine] (Maybe DInTmRN :<: DInTmRN) [CTData]
>   |  DLModule String [DevLine] [CTData]

A module may have a list of definitions in square brackets, followed by
an optional semicolon-separated list of commands.

> parseDevelopment :: Parsley Token [DevLine]
> parseDevelopment  = bracket Square (many (pDef <|> pModule))
>                   <|> pure []

Parsing definitions

A definition is an identifier, followed by a list of children, a
definition (which may be `?`), and optionally a list of commands:

> pDef :: Parsley Token DevLine
> pDef =  DLDef
>     <$> ident                  -- identifier
>     <*> pLines                 -- childrens (optional)
>     <*> pDefn                  -- definition
>     <*> pCTSuffix              -- commands (optional)
>     <* keyword KwSemi

Parsing children:

Children, if any, are enclosed inside square brackets. They can be of
several types: definitions, that we have already defined, or parameters.
Parameters are defined below. The absence of sub-development is signaled
by the `:=` symbol.

> pLines  :: Parsley Token [DevLine]
> pLines  =  bracket Square (many (pDef <|> pParam <|> pModule))
>         <|> (keyword KwDefn *> pure [])

Parsing definitions:

A definition is either a question mark or a term, ascripted by a type.
The question mark corresponds to an open goal. On the other hand, giving
a term corresponds to explicitly solving the goal.

> pDefn :: Parsley Token (Maybe DInTmRN :<: DInTmRN)
> pDefn = (identEq "?" >> keyword KwAsc >> (Nothing :<:) <$> pDInTm)
>     <|> pure pAsc
>   where pAsc = do
>          tm :<: ty <- pAscription
>          return $ Just tm :<: ty

Parsing commands:

Commands can be typed directly in the developments by enclosing them
inside `[| ... |]` brackets. They are parsed in one go by
`pCochonTactics`, so this is quite fragile. This is better used when we
know things work.

> pCTSuffix  :: Parsley Token [CTData]
> pCTSuffix  = bracket (SquareB "") pCochonTactics
>            <|> pure []

Parsing Modules

A module is similar, but has no definition.

> pModule :: Parsley Token DevLine
> pModule =  DLModule
>     <$> ident                  -- identifier
>     <*> pLines                 -- children (optional)
>     <*> pCTSuffix              -- commands (optional)
>     <* keyword KwSemi

Parsing Parameters

A parameter is a $\lambda$-abstraction (represented by `x : T ->`) or
a $\Pi$-abstraction (represented by `(x : S) ->`).

> pParam :: Parsley Token DevLine
> pParam =  (keyword KwLambda        -- @\@
>       $> DLParam ParamLam
>      <*> ident                     -- @x@
>      <*  keyword KwAsc             -- @:@
>      <*> sizedDInTm (pred ArrSize) -- @T@
>      <*  keyword KwArr)            -- @->@
>      <|>
>      bracket Round                 -- @(@
>          (DLParam ParamPi
>               <$> ident            -- @x@
>               <*  keyword KwAsc    -- @:@
>               <*> pDInTm
>          )                         -- @S)@
>      <* keyword KwArr              -- @->@

Construction
------------

Once we have parsed a development as a list of `DevLine`, we interpret
it in the `ProofState` monad. This is the role of `makeDev`. It updates
the proof state to represent the given list of `DevLine`s, accumulating
pairs of names and command lists along the way.

> type NamedCommand = (Name, [CTData])
> makeDev :: [DevLine] -> [NamedCommand] -> ProofState [NamedCommand]
> makeDev []      ncs = return ncs
> makeDev (l:ls)  ncs = makeEntry l ncs >>= makeDev ls

Each line of development is processed by `makeEntry`. This is where the
magic happen and the `ProofState` is updated.

> makeEntry :: DevLine -> [NamedCommand] -> ProofState [NamedCommand]

Making a definition:

To make a definition, we operate in 4 steps. First of all, we jump in a
module in which we make our kids. Once this is done, we resolve our
display syntax goal into a term: we are therefore able to turn the
module in a definition. The third step consists in solving the problem
if we were provided a solution, or give up if not. Finally, we
accumulate the commands which might have been issued.

> makeEntry (DLDef x kids (mtipTm :<: tipTys) commands) ncs = do
>     -- Open a module named by her name
>     n <- makeModule DevelopOther x
>     goIn
>     -- Recursively build the kids
>     ncs' <- makeDev kids ncs
>     -- Translate `tipTys` into a real `INTM`
>     tipTy :=>: tipTyv <- elaborate' (SET :>: tipTys)
>     -- Turn the module into a definition of `tipTy`
>     moduleToGoal tipTy
>     -- Were we provided a solution?
>     case mtipTm of
>         -- No? Leave.
>         Nothing -> goOut
>         Just tms -> do -- Yes!
>             -- Give the solution `tms`
>             elabGive tms
>             return ()
>     -- Is there any tactics to be executed?
>     return $ case commands of
>         -- No? Return the kids' commands.
>         []  -> ncs'
>         -- Yes! Accumulate our commands with the ones from the kids.
>         _   -> (n, commands) : ncs'

Making a Module:

Making a module involves much less effort than to make a definition.
This is indeed a stripped-down version of the above code for
definitions.

> makeEntry (DLModule x kids commands) ncs = do
>     -- Make the module
>     n <- makeModule DevelopModule x
>     goIn
>     -- Recursively build the kids
>     ncs' <- makeDev kids ncs
>     -- Leave
>     goOut
>     -- Is there any tactics to be executed?
>     return $ case commands of
>         -- No? Return the kids' commands.
>         []  -> ncs'
>         -- Yes! Accumulate our commands with the ones from the kids.

>         _   -> (n, commands) : ncs'

Making a Parameter:

To make a parameter, be it Lambda or Pi, is straightforward. First, we
need to translate the type in display syntax to an `INTM`. Then, we make
a fresh reference of that type. Finally, we store that reference in the
development.

> makeEntry (DLParam k x tys) ncs = do
>     -- Translate the display `tys` into an `INTM`
>     ty :=>: tyv <- elaborate' (SET :>: tys)
>     -- Make a fresh reference of that type
>     freshRef (x :<: tyv) (\ref ->
>         -- Register `ref` as a Lambda
>         putEntryAbove (EPARAM ref (mkLastName ref) k ty Nothing))
>     -- Pass the accumulated commands
>     return ncs
