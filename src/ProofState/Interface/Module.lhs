Modules in Proof Context
========================

> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Interface.Module where

> import Control.Monad.Except

> import Kit.BwdFwd
> import Kit.MissingLibrary
> import NameSupply.NameSupply
> import ProofState.Structure.Developments
> import ProofState.Edition.ProofContext
> import ProofState.Edition.Scope
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation
> import ProofState.Interface.Lifting
> import ProofState.Interface.ProofKit
> import Evidences.Tm
> import Evidences.Eval

A module is a pretty dull thing: it is just a name and a development. As
far as I know, there are three usages of modules. The first one is the
one we are used to: introducing namespaces and avoiding name clashes.
This is mostly used at the programming level. For making modules, we use
`makeModule`.

> makeModule :: ModulePurpose -> String -> ProofState Name
> makeModule purpose s = do
>     nsupply <- getDevNSupply
>     let n = mkName nsupply s
>     -- Insert a new entry above, the empty module `s`
>     let dev = Dev {  devEntries       =  B0
>                   ,  devTip           =  Module
>                   ,  devNSupply       =  freshNSpace nsupply s
>                   ,  devSuspendState  =  SuspendNone }
>     putEntryAbove $ EModule  {  name     = n
>                              ,  dev      = dev
>                              ,  expanded = True
>                              ,  purpose  = purpose }
>     putDevNSupply $ freshName nsupply
>     return n

The second usage is more technical, and occurs exclusively in the
implementation (such as in tactics, for instance). It consists in making
a module, going in it, doing some constructions and analyses, and at
some stage wanting to say that this module is actually an open
definition of a certain type (a goal). Turning a module into a goal is
implemented by `moduleToGoal`. An instance of this pattern appears in
Section [Tactics.Elimination.analysis](#Tactics.Elimination.analysis).

> moduleToGoal :: INTM -> ProofState (EXTM :=>: VAL)
> moduleToGoal ty = do
>     (_ :=>: tyv) <- checkHere (SET :>: ty)
>     CModule n expanded _ <- getCurrentEntry
>     inScope <- getInScope
>     let  ty' = liftType inScope ty
>          ref = n := HOLE Waiting :<: evTm ty'
>     putCurrentEntry $ CDefinition LETG ref (last n) ty' AnchNo expanded
>     putDevTip $ Unknown (ty :=>: tyv)
>     return $ applySpine ref inScope

The last usage of modules is to mess around: introducing things in the
proof context to later, in one go, remove it all. One need to be
extremely careful with the removed objects: the risk of introducing
dangling references is high.

> draftModule :: String -> ProofState t -> ProofState t
> draftModule name draftyStuff = do
>     makeModule Draft name
>     goIn
>     t <- draftyStuff
>     goOutBelow
>     mm <- removeEntryAbove
>     case mm of
>         Just (EModule _ _ _ _) -> return t
>         _ -> throwError . sErr $ "draftModule: drafty " ++ name
>                                  ++ " did not end up in the right place!"
