\section{Datatype declaration}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs #-}

> module Tactics.IData where

> import Control.Applicative
> import Control.Monad.Identity
> import Control.Monad.Error

> import Data.Traversable

> import Kit.MissingLibrary

> import Evidences.Tm
> import Evidences.Mangler
> import Evidences.Eval
> import Evidences.Operators
> import Evidences.DefinitionalEquality

> import NameSupply.NameSupplier

> import ProofState.Edition.Scope
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation
> import ProofState.Edition.FakeRef

> import ProofState.Interface.ProofKit
> import ProofState.Interface.Module
> import ProofState.Interface.Definition
> import ProofState.Interface.Parameter
> import ProofState.Interface.Solving
> import ProofState.Interface.NameResolution

> import Elaboration.Elaborator

> import DisplayLang.Name

> import Tactics.Data

%endif



> ielabCons :: String -> INTM -> (EXTM :=>: VAL) -> 
>                [Elim VAL] -> (String , DInTmRN) -> 
>                ProofState ( String          -- con name
>                           , EXTM            -- con ty
>                           , EXTM            -- con desc
>                           )
> ielabCons nom ty (indty :=>: indtyv) ps (s , t) = do
>   make ((s ++ "Ty") :<: ARR ty SET)
>   goIn 
>   r <- lambdaParam nom
>   (tyi :=>: v) <- elabGive' t
>   x <- freshRef ("i" :<: indtyv) 
>         (\i -> ity2desc indty r ps (NP i) (v $$ A (NP r)) >>=
>                  \x -> (| ((L $ "i" :. (capM i 0 %% x))
>                           :? ARR (N indty) 
>                                  (N (P idescREF :$ A (N indty)))) |))
>   goOut
>   return (s, tyi, x)

> ity2desc :: EXTM -> REF -> [Elim VAL] -> VAL -> VAL -> ProofState INTM
> ity2desc indty r ps ind (PI a b) = do
>             let anom = fortran b
>             a' <- bquoteHere a
>             if occurs r a' 
>               then do 
>                 a'' <- ity2h indty r ps a
>                 b' <- freshRef ("betternotturnuplater":<:a)
>                         (\s -> do b' <- ity2desc indty r ps ind (b $$ A (NP s))
>                                   when (occurs s b') $ 
>                                     throwError' (err "Bad dependency")
>                                   return b')
>                 return $ IPROD a'' b'
>               else do 
>                 freshRef (anom :<: a) 
>                  (\s -> ity2desc indty r ps ind (b $$ A (NP s)) >>= 
>                           \x -> 
>                             (| (ISIGMA a' (L $ "a" :. (capM s 0 %% x))) |))
> ity2desc indty r ps i (N (x :$ A i')) = do 
>             b <- withNSupply (equal (SET :>: (N x, NP r $$$ ps)))
>             unless b $ throwError' (err "C doesn't target T")   
>             i'' <- bquoteHere i
>             i''' <- bquoteHere i'
>             return (ICONST (PRF (EQBLUE (N indty :>: i'') (N indty :>: i'''))))
> ity2desc _ _ _ _ _ = throwError' (err "If you think this should work maybe you should have a chat with Dr Morris about it.")

> ity2h :: EXTM -> REF -> [Elim VAL] -> VAL -> ProofState INTM
> ity2h indty r ps (PI a b) = do
>   a' <- bquoteHere a
>   if occurs r a' 
>     then throwError' (err "Not strictly positive")
>     else do
>       b' <- freshRef (fortran b :<: a) 
>               (\s -> ity2h indty r ps (b $$ A (NP s)) >>= \x -> 
>                        (| (L $ "a" :. (capM s 0 %% x) ) |))
>       return (IPI a' b')
> ity2h indty r ps (N (x :$ A i')) = do
>   b <- withNSupply (equal (SET :>: (N x, NP r $$$ ps)))
>   unless b $ throwError' (err "Not SP")   
>   i'' <- bquoteHere i'
>   return (IVAR i'')
> ity2h _ _ _ _ = throwError' (err "If you think this should work maybe you should have a chat with Dr Morris about it.")

> imkAllowed :: (String, EXTM, INTM) -> [(String, EXTM, REF)] -> (INTM, INTM)
> imkAllowed (s, ty, i) = foldr mkAllowedHelp ((ARR (N ty) SET, 
>                                              ALLOWEDCONS  (N ty) 
>                                                           (LK SET)
>                                                           (N (P refl :$ A SET :$ A (ARR (N ty) SET)))
>                                                           i
>                                                           ALLOWEDEPSILON))
>     where mkAllowedHelp (x, ty, r) (allowingTy, allowedTy) =
>             let allowingTy' = L $ x :. (capM r 0 %% allowingTy) in
>             (PI (N ty) allowingTy',
>              ALLOWEDCONS (N ty) allowingTy' (N (P refl :$ A SET :$ A (PI (N ty) allowingTy'))) (NP r) allowedTy)


> ielabData :: String -> [ (String , DInTmRN) ] -> DInTmRN ->
>                        [ (String , DInTmRN) ] -> ProofState (EXTM :=>: VAL)
> ielabData nom pars indty scs = do
>   oldaus <- (| paramSpine getInScope |)
>   makeModule nom
>   goIn
>   pars' <- traverse (\(x,y) -> do  
>     make ((x ++ "ParTy") :<: SET)
>     goIn
>     (yt :=>: yv) <- elabGive y
>     r <- assumeParam (x :<: (N yt :=>: yv))
>     return (x,yt,r)) pars
>   make ("indTy" :<: SET)
>   goIn
>   indty'@(indtye :=>: _) <- elabGive indty
>   moduleToGoal (ARR (N indtye) SET)
>   cs <- traverse (ielabCons nom 
>                   (foldr (\(x,s,r) t -> 
>                             PI (N s) (L $ x :. 
>                               (capM r 0 %% t))) (ARR (N indtye) SET) pars')
>                   indty' (map (\(_,_,r) -> A (NP r)) pars')) scs

>   make ("ConNames" :<: NP enumREF) 
>   goIn
>   (e :=>: ev) <- giveOutBelow (foldr (\(t,_) e -> CONSE (TAG t) e) NILE scs)
>   make ("ConDescs" :<: 
>           ARR (N indtye) (N (branchesOp 
>                               :@ [ N e
>                                  , L $ K (N (P idescREF :$ A (N indtye)))
>                                  ])))
>   goIn
>   i <- lambdaParam "i"
>   (cs' :=>: _) <- giveOutBelow (foldr PAIR VOID (map (\(_,_,c) -> N (c :$ A (NP i))) cs))

>   lt :=>: _ <- getFakeCurrentEntry
>   make ("DataTy" :<: ARR (N indtye) SET)
>   goIn
>   i <- lambdaParam "i"
>   let d = L $ "i" :.IFSIGMA (N e) (N (cs' :$ A (NV 0)))
>       (allowingTy, allowedBy)  =  imkAllowed ("i", indtye, NV 0) pars' -- NV 0 refers to the .i. in the giveOut
>       label                    =  ANCHOR (TAG nom) allowingTy allowedBy
>   (dty :=>: _) <- giveOutBelow (IMU (Just (L $ "i" :. [.i. label])) (N indtye) d (NP i))

We specialise the induction operator to this datatype, ensuring the label is
assigned throughout, so the label will be preserved when eliminating by induction.

This code attempts to find out if the definitions from tests/TaggedInduction
are in scope, if so you get nicer induction principles (:

>   (do (icase,_,_) <- resolveHere [("TData",Rel 0),("tcase",Rel 0)]
>       let caseTm = P icase :$ A (N indtye) :$ A (PAIR (N e) (PAIR (N cs') VOID))
>       caseV :<: caseTy <- inferHere caseTm
>       caseTy' <- bquoteHere caseTy
>       make ("Case" :<: isetLabel (L $ "i" :. [.i. label]) caseTy')
>       goIn
>       giveOutBelow (N caseTm)
>       return ()) `catchError` \_ -> return ()

>   (do (dind,_,_) <- resolveHere [("TData",Rel 0),("tind",Rel 0)]
>       let dindT = P dind :$ A (N indtye) :$ A (PAIR (N e) (PAIR (N cs') VOID))
>       dindV :<: dindTy <- inferHere dindT
>       dindTy' <- bquoteHere dindTy
>       make ("Ind" :<: isetLabel (L $ "i" :. [.i. label]) dindTy')
>       goIn
>       giveOutBelow (N dindT)
>       return ()) `catchError` \_ -> 
>     (do let indTm = P (lookupOpRef iinductionOp) :$ A (N indtye) :$ A d
>         indV :<: indTy <- inferHere indTm
>         indTy' <- bquoteHere indTy
>         make ("Ind" :<: isetLabel (L $ "i" :. [.i. label]) indTy')
>         goIn
>         giveOutBelow (N indTm)
>         return ())
>   giveOutBelow $ N dty


This is a hack, and should probably be replaced with a version that tests for
equality, so it doesn't catch the wrong |MU|s.

> isetLabel :: INTM -> INTM -> INTM
> isetLabel l (IMU Nothing ity tm i) = IMU (Just l) ity tm i
> isetLabel l (IMU (Just (LK (ANCHOR (TAG x) _ _))) ity tm i) | x == "dataTy" = IMU (Just l) ity tm i
> isetLabel l (L (x :. t)) = L (x :. isetLabel l t)
> isetLabel l (L (K t)) = L (K (isetLabel l t))
> isetLabel l (C c) = C (fmap (isetLabel l) c)
> isetLabel l (N n) = N (isetLabelN l n)

> isetLabelN :: INTM -> EXTM -> EXTM
> isetLabelN l (P x) = P x
> isetLabelN l (V n) = V n
> isetLabelN l (op :@ as) = op :@ map (isetLabel l) as
> isetLabelN l (f :$ a) = isetLabelN l f :$ fmap (isetLabel l) a
> isetLabelN l (t :? ty) = isetLabel l t :? isetLabel l ty


> import -> CochonTactics where
>   : CochonTactic
>         {  ctName = "idata"
>         ,  ctParse = do 
>              nom <- tokenString
>              pars <- tokenListArgs (bracket Round $ tokenPairArgs
>                tokenString
>                (keyword KwAsc)
>                tokenInTm) (|()|)
>              keyword KwAsc
>              indty <- tokenAppInTm
>              keyword KwArr
>              keyword KwSet
>              keyword KwDefn
>              scs <- tokenListArgs (bracket Round $ tokenPairArgs
>                tokenString
>                (keyword KwAsc)
>                tokenInTm)
>               (keyword KwSemi)
>              return $ B0 :< nom :< pars :< indty :< scs
>         , ctIO = (\ [StrArg nom, pars, indty, cons] -> simpleOutput $ 
>                     ielabData nom (argList (argPair argToStr argToIn) pars) 
>                      (argToIn indty) (argList (argPair argToStr argToIn) cons)
>                       >> return "Data'd.")
>         ,  ctHelp = "idata <name> [<para>]* : <inx> -> Set  := [(<con> : <ty>) ;]* - builds a data type for thee."
>         } 
