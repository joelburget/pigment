{-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, PatternSynonyms #-}

-- Datatype declaration
-- ====================

module Tactics.Data where

import Control.Applicative
import Control.Error
import Control.Monad.Identity
import Data.Functor.Constant
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
         -- ^ Name of the *type* constructor
         -> INTM
         -- ^ The kind of this data type... Example (defining Either a b), this
         -- is 'a -> b -> SET'
         -> [Elim VAL]
         -- ^ The type parameters
         -> (String , DInTmRN)
         -- ^ Scheme of *this* constructor - the one we're defining
         -> ProofState ElabResult
elabCons dataTyName ty ps (ctorName, ctorScheme) = do
    -- Making a description -- an arrow from the kind of this type to SET.
    -- So...
    --
    -- * 'Either a b' - the data type we're constructing.
    --
    -- * `ty` = `a -> b -> SET`
    --
    -- * Descriptions (only build one per call):
    --
    --   - 'LEFT : (a -> b -> SET) -> SET'
    --
    --   - 'RIGHT : (a -> b -> SET) -> SET'
    make (AnchTy ctorName :<: ARR ty SET)
    goIn
    r <- lambdaParam dataTyName

    -- I guess this constructor's scheme fills the hole we're looking at
    (tyi :=>: v) <- elabGive' ctorScheme

    -- Now actually build the description
    (x, i, j, y) <- ty2desc r ps (v $$ A (NP r))

    goOut
    return $ ElabResult ctorName tyi x i j y


-- | Build a "levitated" description of this type
--
-- Returns:
--
--   1. A description of the data type
--
--   2. The list of argument names
--
--   3. The list of rec (?) argument names
--
--   4. A constructor
ty2desc :: REF
        -- ^ Reference to *this* data type
        -> [Elim VAL]
        -- ^ ?
        -> VAL
        -> ProofState (INTM, [String], [String], [REF] -> INTM)
ty2desc r ps (PI a b) = do
    -- Find something to call b.
    let anom = fortran b
    if occurs r a
      then do
        (a'', i) <- ty2h r ps a
        (b', j, k, c) <- freshRef (fortran b :<: a) $ \s -> do
            ret@(b', _, _, _) <- ty2desc r ps (b $$ A (NP s))
            when (occurs s b') $ throwDTmStr "Bad dependency"
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
                SIGMAD a (L $ "a" :. (capM s 0 %% x)),
                anom : j,
                k,
                \(v:vs) -> PAIR (NP v) (swapM s v %% (y vs))
                )
        freshRef (anom :<: a) $ \s ->
            ty2desc r ps (b $$ A (NP s)) >>= helper s
ty2desc r ps x = do
    b <- withNSupply (equal (SET :>: (x, NP r $$$ ps)))
    unless b $ throwDTmStr "C doesn't target T"
    return (CONSTD UNIT, [], [], \[] -> VOID)


-- | Get a description
ty2h :: REF -> [Elim VAL] -> VAL -> ProofState (INTM, Int)
ty2h r ps (PI a b) = do
    if occurs r a
      then throwDTmStr "Not strictly positive"
      else do
        (b',i) <- freshRef (fortran b :<: a)
                   (\s -> ty2h r ps (b $$ A (NP s)) >>= \(x,y) ->
                                 pure (L $ "a" :. (capM s 0 %% x),y))
        return $ case i of
          0 -> (a , 1)
          _ -> (SIGMA a b', i + 1)
ty2h r ps x = do
    b <- withNSupply $ equal (SET :>: (x, NP r $$$ ps))
    unless b $ throwDTmStr "Not strictly positive"
    return (UNIT, 0)


-- | Find out whether any parameters match the given ref!
--
-- Used to implement the occurs check
occursM :: REF -> Mangle (Constant Any) REF REF
occursM r = Mang
    {  mangP = \ x _ -> Constant (Any (r == x))
    ,  mangV = \ _ _ -> Constant (Any False)
    ,  mangB = \ _ -> occursM r
    }


-- | Swap the occurrences of r and s. Why...
swapM :: REF -> REF -> Mangle Identity REF REF
swapM r s = Mang
    {  mangP = \ x xes ->
                 if x == r then ((P s) $:$) <$> xes
                           else ((P x) $:$) <$> xes
    ,  mangV = \ i ies -> (V i $:$) <$> ies
    ,  mangB = \ _ -> swapM r s
    }


-- | Replace references to r with bound variable i
capM :: REF -> Int -> Mangle Identity REF REF
capM r i = Mang
    {  mangP = \ x xes ->
                 if x == r then ((V i) $:$) <$> xes
                           else ((P x) $:$) <$> xes
    ,  mangV = \ j jes -> (V j $:$) <$> jes
    ,  mangB = \ _ -> capM r (i+1)
    }


-- | Does the ref occur anywhere in the term?
occurs :: REF -> INTM -> Bool
occurs r i = getAny (getConstant (occursM r % i))

-- | Uncurry v (with i remaining tuple pieces)
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


-- Fold over all the type parameters, building up
mkAllowed :: [Parameter] -> (INTM, INTM)
mkAllowed = foldr mkAllowedHelp (SET, ALLOWEDEPSILON) where
    mkAllowedHelp p (allowingTy, allowedTy) =

        let x = paramName p
            ty = paramTy p
            r = paramRef p

            -- Turn allowingTy into a lambda taking x as a parameter
            allowingTy' = L $ x :. (capM r 0 %% allowingTy)

            -- Nevermind, we actually want 'Pi(ty, \n -> allowingTy)'
            allowingTy'' = PI (N ty) allowingTy'

            --
            allowedBy = ALLOWEDCONS
                (N ty)
                allowingTy'
                (N (P refl :$ A SET :$ A allowingTy''))
                (NP r)
                allowedTy
        in (allowingTy'', allowedBy)


emptyData :: String
          -> ProofState (EXTM :=>: VAL)
emptyData name = do
    makeModule DevelopData name
    goIn
    moduleToGoal SET


-- XXX huge TODO:
-- figure out how to handle changes when this thing is in use
addTypeParam :: (String, DInTmRN) -> ProofState REF -- (EXTM :=>: VAL)
addTypeParam (name, ty) = do
    make $ AnchParTy name :<: SET
    goIn
    tyTm :=>: tyVal <- elabGive ty
    assumeParam (name :<: (N tyTm :=>: tyVal))


addConstructor :: String
               -- ^ Name of the type constructor
               --
               -- TODO(joel) I'm sure this can be recovered reliably from the
               -- context
               -> (String, DInTmRN)
               -- ^ Name and scheme of constructor to build
               --
               -- TODO(joel) curry?
               -> ProofState ()
addConstructor tyName (name, scheme) = do
    CDefinition LETG ref@(n := (_ :<: ty)) _ _ anch meta <- getCurrentEntry

    -- SCRATCH
          elabCons nom

                   -- type pointing from all the type parameters to SET
                   (foldr (\(x,s,r) t -> PI (N s) (L $ x :. (capM r 0 %% t)))
                          SET
                          pars')

                   -- apply to all the parameters
                   (map (\(_, _, r) -> A (NP r)) pars')
    -- END SCRATCH

    let parameters = undefined
        elims = map (A . NP . paramRef) parameters

    -- first build the description
    elabCons tyName tyTyTODO elims (name, scheme)

    -- now build the actual constructor


data Parameter = Parameter
    { paramName :: String
    , paramTy   :: EXTM
    , paramRef  :: REF
    }


elabData :: String
         -- ^ Name of the data type
         -> [ (String , DInTmRN) ]
         -- ^ Parameters (Name, Type)
         -> [ (String , DInTmRN) ]
         -- ^ Schemes (Name, Type)
         -> ProofState (EXTM :=>: VAL)
elabData nom pars schemes = do
      oldaus <- paramSpine <$> getInScope

      -- start by making a module named after the type of what we're
      -- building
      makeModule DevelopData nom

      -- we're going to be working inside of the module for the rest of
      -- this function
      goIn

      -- make a goal to solve the type of each parameter
      pars' <- for pars $ \(x, y) -> do
          make $ (AnchParTy x) :<: SET
          goIn
          yt :=>: yv <- elabGive y
          r <- assumeParam (x :<: (N yt :=>: yv))

          -- name, type, param ref
          return (Parameter x yt r)

      moduleToGoal SET

      -- we need to figure out the type of all the constructors
      cs <- for schemes $ elabCons
          nom

          -- type pointing from all the type parameters to SET
          (foldr
              (\p tyAccum -> PI
                  (N (paramTy p))
                  (L $ (paramName p) :. (capM (paramRef p) 0 %% tyAccum))
              )
              SET
              pars'
          )

          -- apply to all the parameters
          (map (A . NP . paramRef) pars')

      -- and constructor names
      make (AnchConNames :<: NP enumREF)
      goIn
      (e :=>: ev) <- giveOutBelow (foldr (\(t,_) e -> CONSE (TAG t) e) NILE schemes)

      -- ... constructor descriptions?
      make (AnchConDescs :<: N (branchesOp :@ [ N e, LK (NP descREF)])) -- ARR (ENUMT (N e)) (NP descREF)
      goIn
      (cs' :=>: _) <- giveOutBelow $ foldr PAIR VOID $ map conDesc cs

      makeKinded Waiting (AnchDataDesc :<: NP descREF)
      goIn
      (d :=>: dv) <- giveOutBelow
          (SUMD (N e)
                (L ("s" :. N (switchDOp :@ [N e, N cs', NV 0]))))
      -- lt :=>: _ <- getFakeCurrentEntry XXX

      -- the type of the data type we just created is Set
      make ((AnchDataTy nom) :<: SET)
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

--       makeModule DevelopOther "Ind"
--       goIn
--       v <- assumeParam
--         (allCommonPrefix (concatMap recArgNames cs) :<: (N dty :=>: dtyv))
--       let indTm = P (lookupOpRef inductionOp) :$ A (N d) :$ A (NP v)
--       indV :<: indTy <- inferHere indTm
--       moduleToGoal (setLabel anchor indTy)
--       giveOutBelow (N indTm)

      giveOutBelow $ N dty

-- | Find the prefix where the two lists match
--
-- >>> commonPrefix [1,2,3] [2,1,3]
-- []
--
-- >>> commonPrefix [1,2,3] [1,2,4]
-- [1,2]
commonPrefix :: Eq a => [a] -> [a] -> [a]
commonPrefix [] _ = []
commonPrefix _ [] = []
commonPrefix (a : as) (b : bs) | a == b = a : commonPrefix as bs
commonPrefix (a : as) (b : bs) = []

-- | Find the prefix where all the lists match
--
-- >>> allCommonPrefix [[1,2,3],[1,2,4],[1,2,5]]
-- [1,2]
--
-- >>> allCommonPrefix [[1,2,3],[2,1,3]]
-- []
allCommonPrefix :: Eq a => [[a]] -> [a]
allCommonPrefix [] = []
allCommonPrefix (as : ass) = foldr commonPrefix as ass

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
