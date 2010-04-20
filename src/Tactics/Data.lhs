\section{Datatype declaration}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs #-}

> module Tactics.Data where

> import Control.Applicative
> import Control.Monad.Identity

> import Data.Monoid hiding (All)
> import Data.Traversable

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import Evidences.Tm
> import Evidences.Rules
> import Evidences.Mangler

> import NameSupply.NameSupplier

> import ProofState.Developments
> import ProofState.ProofContext
> import ProofState.ProofState
> import ProofState.ProofKit

> import Elaboration.Elaborator

> import DisplayLang.DisplayTm

%endif



> elabCons :: String -> INTM -> [Elim VAL] -> (String , InDTmRN) -> 
>             ProofState ( String          -- con name
>                        , EXTM            -- con ty
>                        , INTM            -- con desc
>                        , [String]        -- arg names
>                        , [REF] -> INTM   -- smart con body
>                        )
> elabCons nom ty ps (s , t) = do
>             make ((s ++ "Ty") :<: ARR ty SET)
>             goIn 
>             r <- lambdaBoy nom
>             (tyi :=>: v) <- elabGive' t
>             (x,i,y) <- ty2desc r ps (v $$ A (NP r))
>             goOut
>             return (s, tyi, x, i, y)

> ty2desc :: REF -> [Elim VAL] -> VAL -> 
>            ProofState (INTM, [String], [REF] -> INTM)
> ty2desc r ps (PI a b) = do
>             let anom = fortran b
>             a' <- bquoteHere a
>             if occurs r a' 
>               then do 
>                 (a'',i) <- ty2h r ps a
>                 (b',j,c) <- freshRef ("betternotturnuplater":<:a)
>                             (\s -> do (b',j,c) <- ty2desc r ps (b $$ A (N (P s)))
>                                       when (occurs s b') $ 
>                                         throwError' (err "Bad dependency")
>                                       return (b',j,c))
>                 case i of
>                   0 -> return $ (PRODD IDD  b', anom : j,\(v:vs) -> PAIR (NP v) (c vs))
>                   _ -> return $ (PRODD (PID a'' IDD) b' , anom : j
>                                 , \(v:vs) -> PAIR (L $ anom :. uncur i (P v) (V 0))
>                                                   (c vs))
>               else do 
>                 freshRef (anom :<: a) 
>                  (\s -> ty2desc r ps (b $$ A (NP s)) >>= 
>                           \(x,j,y) -> 
>                             (| ( SIGMAD a' (L $ "a" :. (capM s 0 %% x)), anom : j
>                                , \(v:vs) -> PAIR (NP v) (swapM s v %% (y vs))) |))
> ty2desc r ps x = do 
>             b <- withNSupply (equal (SET :>: (x, NP r $$$ ps)))
>             unless b $ throwError' (err "C doesn't target T")   
>             return (CONSTD UNIT,[],\[] -> VOID)

> ty2h :: REF -> [Elim VAL] -> VAL -> ProofState (INTM,Int)
> ty2h r ps (PI a b) = do
>             a' <- bquoteHere a
>             if occurs r a' 
>               then throwError' (err "Not strictly positive")
>               else do
>                 (b',i) <- freshRef (fortran b :<: a) 
>                            (\s -> ty2h r ps (b $$ A (NP s)) >>= \(x,y) -> 
>                                          (| (L $ "a" :. (capM s 0 %% x),y) |))
>                 case i of
>                   0 -> return ( a' , 1 ) 
>                   _ -> return ( SIGMA a' b', i + 1 ) 
> ty2h r ps x = do
>             b <- withNSupply (equal (SET :>: (x, NP r $$$ ps)))
>             unless b $ throwError' (err "Not SP")   
>             return (UNIT,0)

> occursM :: REF -> Mangle (Ko Any) REF REF
> occursM r = Mang
>             {  mangP = \ x _ -> Ko (Any (r == x))
>             ,  mangV = \ _ _ -> Ko (Any False)
>             ,  mangB = \ _ -> occursM r
>             }

> swapM :: REF -> REF -> Mangle Identity REF REF
> swapM r s = Mang
>             {  mangP = \ x xes -> 
>                          if x == r then (| ((P s) $:$) xes |) 
>                                    else (| ((P x) $:$) xes |)
>             ,  mangV = \ i ies -> (|(V i $:$) ies|)
>             ,  mangB = \ _ -> swapM r s
>             }

> capM :: REF -> Int -> Mangle Identity REF REF
> capM r i = Mang
>             {  mangP = \ x xes -> 
>                          if x == r then (| ((V i) $:$) xes |) 
>                                    else (| ((P x) $:$) xes |)
>             ,  mangV = \ j jes -> (|(V j $:$) jes|)
>             ,  mangB = \ _ -> capM r (i+1)
>             }

> occurs :: REF -> INTM -> Bool
> occurs r i = getAny (unKo (occursM r % i))

> uncur 1 v t = N (v :$ A (N t))
> uncur i v t = uncur (i-1) (v :$ A (N (t :$ Fst))) (t :$ Snd)

> makeCon e t (s,ty,_,i,body) = do
>             make (s :<: N (ty :$ A t))
>             goIn
>             make ("conc" :<: ENUMT e)
>             goIn
>             (c :=>: _) <- elabGive (DTAG s)
>             rs <- traverse (\x -> lambdaBoy x) i
>             give $ CON (PAIR (N c) (body rs))
>             return ()


> elabData :: String -> [ (String , InDTmRN) ] -> 
>                       [ (String , InDTmRN) ] -> ProofState (EXTM :=>: VAL)
> elabData nom pars scs = do
>       oldaus <- (| boySpine getAuncles |)
>       makeModule nom
>       goIn
>       pars' <- traverse (\(x,y) -> do  
>         make ((x ++ "ParTy") :<: SET)
>         goIn
>         (yt :=>: yv) <- elabGive y
>         r <- lambdaBoy' (x :<: (N yt :=>: yv))
>         return (x,yt,r)) pars
>       moduleToGoal SET
>       cs <- traverse (elabCons nom 
>                       (foldr (\(x,s,r) t -> PI (N s) (L $ x :. 
>                                               (capM r 0 %% t))) SET pars')
>                       (map (\(_,_,r) -> A (NP r)) pars')) scs
>       make ("ConNames" :<: NP enumREF) 
>       goIn
>       (e :=>: ev) <- give (foldr (\(t,_) e -> CONSE (TAG t) e) NILE scs)
>       make ("ConDescs" :<: ARR (ENUMT (N e)) (NP descREF)) --(N (branchesOp :@ [ N e, L $ K (NP descREF)])))
>       goIn
>       (cs' :=>: _) <- elabGive (foldr (\c t -> DPAIR (DTIN c) t) DVOID 
>                                 (map (\(_,_,c,_,_) -> c) cs))
>       make ("DataDesc" :<: NP descREF)
>       goIn
>       (d :=>: dv) <- give (SIGMAD (ENUMT (N e)) (N cs'))
>       GirlMother (nom := HOLE _ :<: ty) _ _ _ <- getMother
>       let fr = nom := FAKE :<: ty
>       xs <- (| boySpine getAuncles |)
>       let lt = N (P fr $:$ xs)
>       make ("DataTy" :<: SET)
>       goIn
>       (dty :=>: _) <- give (MU (Just lt) (N d))
>       E r _ _ _ <- getDevEntry
>       traverse (makeCon (N e) (N (P r $:$ oldaus))) cs
>       x <- give $ N dty
>       return x

> import -> CochonTactics where
>   : CochonTactic
>         {  ctName = "data"
>         ,  ctParse = do 
>              nom <- tokenString
>              pars <- tokenListArgs (bracket Round $ tokenPairArgs
>                tokenString
>                (keyword KwAsc)
>                tokenInTm) (|()|)
>              keyword KwDefn
>              scs <- tokenListArgs (bracket Round $ tokenPairArgs
>                tokenString
>                (keyword KwAsc)
>                tokenInTm)
>               (keyword KwSemi)
>              return $ B0 :< nom :< pars :< scs
>         , ctIO = (\ [StrArg nom, pars, cons] -> simpleOutput $ 
>                     elabData nom (argList (argPair argToStr argToIn) pars) 
>                                  (argList (argPair argToStr argToIn) cons) 
>                       >> return "Data'd.")
>         ,  ctHelp = "data <name> [<para>]* := [(<con> : <ty>) ;]* - builds a data type for thee."
>         } 