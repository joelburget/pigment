{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, PatternSynonyms #-}

-- Datatype declaration
-- ====================

module Tactics.Data where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Identity
import Data.Monoid hiding (All)
import Data.Traversable
import Kit.MissingLibrary
import Evidences.Tm
import Evidences.Mangler
import Evidences.Eval
import Evidences.Operators
import Evidences.DefinitionalEquality
import NameSupply.NameSupplier
import ProofState.Structure.Developments
import ProofState.Edition.Scope
import ProofState.Edition.ProofState
import ProofState.Edition.GetSet
import ProofState.Edition.Navigation
import ProofState.Edition.FakeRef
import ProofState.Interface.ProofKit
import ProofState.Interface.Module
import ProofState.Interface.Definition
import ProofState.Interface.Parameter
import ProofState.Interface.Solving
import Elaboration.Elaborator
import DisplayLang.DisplayTm
import DisplayLang.Name

-- Elaborate constructor.

data ElabResult = ElabResult
    { conName     :: String          -- con name
    , conTy       :: EXTM            -- con ty
    , conDesc     :: INTM            -- con desc
    , argNames    :: [String]        -- arg names
    , recArgNames :: [String]        -- rec arg names
    , conBody     :: ([REF] -> INTM) -- smart con body
    }

elabCons :: String
         -> INTM
         -> [Elim VAL]
         -> (String , DInTmRN)
         -> ProofState ElabResult
elabCons nom ty ps (s, t) = do
    make ((AnchTy s) :<: ARR ty SET)
    goIn
    r <- lambdaParam nom
    (tyi :=>: v) <- elabGive' t
    (x, i, j, y) <- ty2desc r ps (v $$ A (NP r))
    goOut
    return $ ElabResult s tyi x i j y

ty2desc :: REF -> [Elim VAL] -> VAL ->
           ProofState (INTM, [String], [String], [REF] -> INTM)
ty2desc r ps (PI a b) = do
    let anom = fortran b
    a' <- bquoteHere a
    if occurs r a'
      then do
        (a'', i) <- ty2h r ps a
        (b', j, k, c) <- freshRef (fortran b :<: a) $ \s -> do
            ret@(b', _, _, _) <- ty2desc r ps (b $$ A (N (P s)))
            when (occurs s b') $ throwError (sErr "Bad dependency")
            return ret
        case i of
          0 -> return (
              PRODD (TAG anom) IDD b',
              anom : j,
              anom : k,
              \(v:vs) -> PAIR (NP v) (c vs)
              )
          _ -> return (
              PRODD (TAG anom) (PID a'' IDD) b',
              anom : j,
              anom : k,
              \(v:vs) -> PAIR (L $ anom :. uncur i (P v) (V 0)) (c vs)
              )
      else do
        let helper s (x, j, k, y) = return (
                SIGMAD a' (L $ "a" :. (capM s 0 %% x)),
                anom : j,
                k,
                \(v:vs) -> PAIR (NP v) (swapM s v %% (y vs))
                )
        freshRef (anom :<: a) $ \s ->
            ty2desc r ps (b $$ A (NP s)) >>= helper s
ty2desc r ps x = do
    b <- withNSupply (equal (SET :>: (x, NP r $$$ ps)))
    unless b $ throwError (sErr "C doesn't target T")
    return (CONSTD UNIT, [], [], \[] -> VOID)

ty2h :: REF -> [Elim VAL] -> VAL -> ProofState (INTM, Int)
ty2h r ps (PI a b) = do
    a' <- bquoteHere a
    if occurs r a'
      then throwError (sErr "Not strictly positive")
      else do
        (b',i) <- freshRef (fortran b :<: a)
                   (\s -> ty2h r ps (b $$ A (NP s)) >>= \(x,y) ->
                                 (| (L $ "a" :. (capM s 0 %% x),y) |))
        return $ case i of
          0 -> (a' , 1)
          _ -> (SIGMA a' b', i + 1)
ty2h r ps x = do
    b <- withNSupply $ equal (SET :>: (x, NP r $$$ ps))
    unless b $ throwError (sErr "Not SP")
    return (UNIT, 0)

occursM :: REF -> Mangle (Ko Any) REF REF
occursM r = Mang
    {  mangP = \ x _ -> Ko (Any (r == x))
    ,  mangV = \ _ _ -> Ko (Any False)
    ,  mangB = \ _ -> occursM r
    }

swapM :: REF -> REF -> Mangle Identity REF REF
swapM r s = Mang
    {  mangP = \ x xes ->
                 if x == r then (| ((P s) $:$) xes |)
                           else (| ((P x) $:$) xes |)
    ,  mangV = \ i ies -> (|(V i $:$) ies|)
    ,  mangB = \ _ -> swapM r s
    }

capM :: REF -> Int -> Mangle Identity REF REF
capM r i = Mang
    {  mangP = \ x xes ->
                 if x == r then (| ((V i) $:$) xes |)
                           else (| ((P x) $:$) xes |)
    ,  mangV = \ j jes -> (|(V j $:$) jes|)
    ,  mangB = \ _ -> capM r (i+1)
    }

occurs :: REF -> INTM -> Bool
occurs r i = getAny (unKo (occursM r % i))

uncur :: Int -> EXTM -> EXTM -> INTM
uncur 1 v t = N (v :$ A (N t))
uncur i v t = uncur (i - 1) (v :$ A (N (t :$ Fst))) (t :$ Snd)

makeCon :: INTM -> INTM -> ElabResult -> ProofState ()
makeCon e t (ElabResult s ty _ i _ body) = do
    make (AnchConName s :<: N (ty :$ A t))
    goIn
    make (AnchConc :<: ENUMT e)
    goIn
    c :=>: _ <- elabGive (DTAG s)
    rs <- for i lambdaParam
    giveOutBelow $ CON (PAIR (N c) (body rs))
    return ()

mkAllowed :: [(String, EXTM, REF)] -> (INTM, INTM)
mkAllowed = foldr mkAllowedHelp (SET, ALLOWEDEPSILON) where
    mkAllowedHelp (x, ty, r) (allowingTy, allowedTy) =
        let allowingTy' = L $ x :. (capM r 0 %% allowingTy)
            allowingTy'' = PI (N ty) allowingTy'
            allowedBy = ALLOWEDCONS
                (N ty)
                allowingTy'
                (N (P refl :$ A SET :$ A (PI (N ty) allowingTy')))
                (NP r)
                allowedTy
        in (allowingTy'', allowedBy)

elabData :: String -> [ (String , DInTmRN) ] ->
                      [ (String , DInTmRN) ] -> ProofState (EXTM :=>: VAL)
elabData nom pars scs = do
      oldaus <- (| paramSpine getInScope |)

      -- start by making a module named after the type of what we're
      -- building
      makeModule nom

      -- we're going to be working inside of the module for the rest of
      -- this function
      goIn

      -- make a goal to solve the type of each parameter
      pars' <- for pars $ \(x, y) -> do
          make $ (AnchParTy x) :<: SET
          goIn
          yt :=>: yv <- elabGive y
          r <- assumeParam (x :<: (N yt :=>: yv))
          return (x, yt, r)

      moduleToGoal SET

      -- we need to figure out the type of all the constructors
      cs <- for scs $
          elabCons nom
                   (foldr (\(x,s,r) t -> PI (N s) (L $ x :. (capM r 0 %% t)))
                          SET
                          pars')
                   (map (\(_, _, r) -> A (NP r)) pars')

      -- and constructor names
      make (AnchConNames :<: NP enumREF)
      goIn
      (e :=>: ev) <- giveOutBelow (foldr (\(t,_) e -> CONSE (TAG t) e) NILE scs)

      -- ... constructor descriptions?
      make (AnchConDescs :<: N (branchesOp :@ [ N e, L $ K (NP descREF)])) -- ARR (ENUMT (N e)) (NP descREF)
      goIn
      (cs' :=>: _) <- giveOutBelow $ foldr PAIR VOID $ map conDesc cs

      makeKinded (AnchStr nom) Waiting (AnchDataDesc :<: NP descREF)
      goIn
      (d :=>: dv) <- giveOutBelow
          (SUMD (N e)
                (L ("s" :. N (switchDOp :@ [N e, N cs', NV 0]))))
      -- lt :=>: _ <- getFakeCurrentEntry XXX

      -- the type of the data type we just created is Set
      make (AnchDataTy :<: SET)
      goIn
      let (allowingTy, allowedBy) = mkAllowed pars'
          anchor = ANCHOR (TAG nom) allowingTy allowedBy
      (dty :=>: dtyv) <- giveOutBelow (MU (Just anchor) (N d))
      EEntity r _ _ _ _ _ <- getEntryAbove

      -- make the constructors
      for cs $ makeCon (N e) (N (P r $:$ oldaus))

      -- We specialise the induction operator to this datatype, ensuring
      -- the label is assigned throughout, so the label will be preserved
      -- when eliminating by induction.

      makeModule "Ind"
      goIn
      v <- assumeParam
        (comprefold (concatMap recArgNames cs) :<: (N dty :=>: dtyv))
      let indTm = P (lookupOpRef inductionOp) :$ A (N d) :$ A (NP v)
      indV :<: indTy <- inferHere indTm
      indTy' <- bquoteHere indTy
      moduleToGoal (setLabel anchor indTy')
      giveOutBelow (N indTm)

      giveOutBelow $ N dty

compre :: Eq a => [a] -> [a] -> [a]
compre [] _ = []
compre _ [] = []
compre (a : as) (b : bs) | a == b = a : compre as bs
compre (a : as) (b : bs) = []

comprefold :: Eq a => [[a]] -> [a]
comprefold [] = []
comprefold (as : ass) = foldr compre as ass

-- This is a hack, and should probably be replaced with a version that
-- tests for equality, so it doesn't catch the wrong `MU`s.

setLabel :: INTM -> INTM -> INTM
setLabel l (MU Nothing tm) = MU (Just l) tm
setLabel l (L (x :. t)) = L (x :. setLabel l t)
setLabel l (L (K t)) = L (K (setLabel l t))
setLabel l (C c) = C (fmap (setLabel l) c)
setLabel l (N n) = N (setLabelN l n)

setLabelN :: INTM -> EXTM -> EXTM
setLabelN l (P x) = P x
setLabelN l (V n) = V n
setLabelN l (op :@ as) = op :@ map (setLabel l) as
setLabelN l (f :$ a) = setLabelN l f :$ fmap (setLabel l) a
setLabelN l (t :? ty) = setLabel l t :? setLabel l ty
