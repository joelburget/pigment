<a name="Cochon.Reactify">Pretty-printing</a>
===============

> {-# LANGUAGE ScopedTypeVariables, GADTs, FlexibleInstances, TypeOperators,
>     TypeSynonymInstances, OverloadedStrings, PatternSynonyms,
>     LiberalTypeSynonyms, FlexibleContexts #-}

> module Cochon.Reactify where

> import Data.Functor.Identity
> import Data.List
> import Data.Monoid ((<>))
> import Data.String (fromString)

> import Cochon.Model
> import ProofState.Structure.Developments
> import Distillation.Distiller
> import Distillation.Scheme
> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.Scheme
> import DisplayLang.Lexer
> import Evidences.Tm
> import Kit.BwdFwd
> import Kit.MissingLibrary hiding ((<>))
> import ProofState.Edition.ProofState

> import React hiding (key)

> import DisplayLang.PrettyPrint
> import Kit.Trace
> import Debug.Trace

The `reactKword` function gives a react element representing a `Keyword`.

> reactKword :: Keyword -> React a b c ()
> reactKword kw = div_ [ class_ "kw" ] $ case kw of
>     KwArr -> span_ [ class_ "kw-arr" ] $ return ()
>     KwImp -> span_ [ class_ "kw-imp" ] $ return ()
>     KwLambda -> span_ [ class_ "kw-lambda" ] $ return ()
>     _ -> fromString (key kw)

> reactBrackets :: Bracket -> React a b c d -> React a b c ()
> reactBrackets br r = do
>     fromString (showOpenB br)
>     _ <- r
>     fromString (showCloseB br)

The `Reactive` class describes things that can be made into React
elements.

> class Reactive x where
>     reactify :: x -> TermReact

> instance Reactive (Can DInTmRN) where
>     reactify x = div_ [ class_ "can-dintmrn" ] $ canReactify x

> canReactify :: Can DInTmRN -> TermReact
> canReactify Set       = reactKword KwSet
> canReactify (Pi s t)  = reactPi (DPI s t)
> canReactify (Label l t) = div_ [ class_ "can-label" ] $ do
>     reactify l
>     reactKword KwAsc
>     reactify t

> canReactify (Con x)   = reactKword KwCon >> reactify x

  canReactify (Anchor (DTAG u) t ts) = fromString u >> reactify ts
  canReactify AllowedEpsilon = ""
  canReactify (AllowedCons _ _ _ s ts) = reactify s >> reactify ts

> canReactify (Mu (Just l   :?=: _)) = reactify l
> canReactify (Mu (Nothing  :?=: Identity t)) = reactKword KwMu >> reactify t

  canReactify (EnumT t)  = reactKword KwEnum >> reactify t
  canReactify Ze         = "0"
  canReactify (Su t)     = reactifyEnumIndex 1 t
  canReactify (EqBlue pp qq) = reactify (DEqBlue (foo pp) (foo qq))
    where
      foo :: (DInTmRN :>: DInTmRN) -> DExTmRN
      foo (_    :>: DN x  ) = x
      foo (xty  :>: x     ) = DType xty ::$ [A x]
  canReactify (Monad d x)   = reactKword KwMonad >> reactify d >> reactify x
  canReactify (Return x)    = div_ [ class_ "can-return" ] $ do
      reactKword KwReturn
      reactify x
  canReactify (Composite x) = reactKword KwCon >> reactify x
  canReactify (IMu (Just l   :?=: _) i)  = reactify l >> reactify i
  canReactify (IMu (Nothing  :?=: (Identity ii :& Identity d)) i)  = do
      reactKword KwIMu
      reactify ii
      reactify d
      reactify i

> canReactify (LRet x) = reactKword KwRet >> reactify (traceShowId x)

  canReactify (Nu (Just l :?=: _))  = reactify l
  canReactify (Nu (Nothing :?=: Identity t))  = reactKword KwNu >> reactify t
  canReactify (CoIt d sty f s) = do
      reactKword KwCoIt
      reactify sty
      reactify f
      reactify s
  canReactify Prop           = reactKword KwProp

> canReactify (Prf p)        = reactKword KwPrf >> reactify p

  canReactify (All p q)      = reactifyAll "" (DALL p q)
  canReactify (And p q)      = reactify p >> reactKword KwAnd >> reactify q
  canReactify Trivial        = reactKword KwTrivial
  canReactify Absurd         = reactKword KwAbsurd
  canReactify (Box (Irr p))  = reactify p
  canReactify (Inh ty)       = reactKword KwInh >> reactify ty
  canReactify (Wit t)        = reactKword KwWit >> reactify t
  canReactify (Quotient x r p) = do
      reactKword KwQuotient
      mapM_ reactify [x,r,p]
  canReactify RSig              =  "RSignature"
  canReactify REmpty            =  "empty"
  canReactify (RCons s i t)     = do
      reactify s
      ">"
      reactify i
      " , "
      reactify t
  canReactify Unit         = reactKword KwSig >> "()"
  canReactify Void         = reactifyPair DVOID

> canReactify (Sigma s t)  = reactifySigma "" (DSIGMA s t)
> canReactify (Pair a b)   = reactifyPair (DPAIR a b)

  canReactify UId      = reactKword KwUId
  canReactify (Tag s)  = reactKword KwTag >> fromString s

> canReactify can       = fromString $ "TODO(joel) - " ++ show can

`reactPi` accumulates domains until a non-dependent pi is found.

> reactPi :: DInTmRN -> TermReact
> reactPi tm = div_ [ class_ "pi" ] $ do
>     -- elabTrace $ renderHouseStyle $ pretty tm PiSize
>     reactPi' tm

> reactPi' :: DInTmRN -> TermReact
> -- IE `s -> t`
> reactPi' (DPI s (DL (DK t))) = do
>     reactify s
>     reactKword KwArr
>     reactify t
> -- IE `(x : s) -> t`
> reactPi' (DPI s (DL (x ::. t))) = do
>     reactBrackets Round $ do
>         fromString x
>         reactKword KwAsc
>         reactify s
>     -- TODO(joel) we don't *always* want this arrow here. it's not a huge
>     -- deal for now - nobody will notice, but it would be nice to elide
>     -- arrows
>     reactKword KwArr
>     reactPi' t
> -- IE `pi s t`
> reactPi' (DPI s t) = do
>     reactKword KwPi
>     reactify s
>     reactify t
> -- IE `tm`
> reactPi' tm = reactify tm

The `reactPiMore` function takes a bunch of domains (which may be empty)
and a codomain, and represents them appropriately for the current size.

> reactPiMore :: TermReact -> TermReact -> TermReact
> reactPiMore bs d = bs >> reactKword KwArr >> d

To reactify a scope, we accumulate arguments until something other than
a lambda term is reached.

> instance Reactive DSCOPE where
>     reactify s = reactLambda (B0 :< dScopeName s) (dScopeTm s)

> reactLambda :: Bwd String -> DInTmRN -> TermReact
> reactLambda vs (DL s) = reactLambda (vs :< dScopeName s) (dScopeTm s)
> reactLambda vs tm = div_ [ class_ "lambda" ] $ do
>     reactKword KwLambda
>     reactBrackets Round $ fromString $ unwords $ trail vs
>     reactKword KwArr
>     reactify tm

> handleLambdaContext, handleCanonicalContext, handleNeutralContext, handleQuestionContext, handleUnderscoreContext :: MouseEvent -> Maybe TermAction
> handleLambdaContext = undefined
> handleCanonicalContext = undefined
> handleNeutralContext = undefined
> handleQuestionContext = undefined
> handleUnderscoreContext = undefined

> instance Reactive DInTmRN where
>     reactify (DL s)          =
>         div_ [ class_ "dintmrn-canonical"
>              -- , onClick (handleLambdaContext s)
>              ] $
>             reactify s
>     reactify (DC c)          =
>         div_ [ class_ "dintmrn-canonical"
>              -- , onClick (handleCanonicalContext c)
>              ] $
>             reactify c
>     reactify (DN n)          =
>         div_ [ class_ "dintmrn-neutral"
>              -- , onClick (handleNeutralContext n)
>              ] $
>             reactify n
>     reactify (DQ x)          =
>         div_ [ class_ "dintmrn-question"
>              -- , onClick (handleQuestionContext x)
>              ] $
>             fromString $ '?':x
>     reactify DU              =
>         div_ [ class_ "dintmrn-underscore"
>              -- TODO(joel) - provide some info so we can locate this
>              -- underscore!
>              -- , onClick (handleUnderscoreContext)
>              ] $
>             reactKword KwUnderscore

      reactify (DEqBlue t u) = reactify t >> reactKword KwEqBlue >> reactify u
      reactify (DIMu (Just s   :?=: _) _) = reactify s
      reactify (DIMu (Nothing  :?=: (Identity ii :& Identity d)) i) = do
          reactKword KwIMu
          reactify ii
          reactify d
          reactify i

>     reactify (DAnchor name _)  = fromString name

      reactify (DTAG name)        = reactKword KwTag >> fromString name
      reactify (DTag name tms) = do
          reactKword KwTag
          fromString name
          mapM_ reactify tms

>     reactify indtm           = fromString $ "TODO(joel) - " ++ show indtm

> instance Reactive DExTmRN where
>     reactify (n ::$ els)  = div_ [ class_ "dextmrn" ] $ do
>         reactify n
>         mapM_ reactify els

> instance Reactive DHEAD where
>     reactify dh = div_ [ class_ "dhead" ] $ reactify' dh where
>         -- Parameter (RelName)
>         -- TODO(joel) this is the same as `reasonableName`
>         reactify' (DP x)       = fromString $ fst $ last x
>         reactify' (DType ty)   = reactKword KwAsc >> reactify ty
>         reactify' (DTEx ex)    = "TODO(joel) - DTEx"

> instance Reactive (Scheme DInTmRN) where
>     reactify sch = div_ [ class_ "scheme-dintmrn" ] $ reactify' sch where
>
>         reactify' (SchType ty) = reactKword KwAsc >> reactify ty
>         reactify' (SchExplicitPi (x :<: schS) schT) = do
>             reactBrackets Round (fromString x >> reactify schS)
>             reactify schT
>         reactify' (SchImplicitPi (x :<: s) schT) = do
>             reactBrackets Square $ do
>                 fromString x
>                 reactKword KwAsc
>                 reactify s
>             reactify schT

  reactifyEnumIndex :: Int -> DInTmRN -> Pure React'
  reactifyEnumIndex n DZE      = fromString $ show n
  reactifyEnumIndex n (DSU t)  = reactifyEnumIndex (succ n) t
  reactifyEnumIndex n tm       = do
      fromString (show n)
      reactKword KwPlus
      reactify tm

  reactifyAll :: Pure React' -> DInTmRN -> Pure React'
  reactifyAll bs (DALL (DPRF p) (DL (DK q))) = reactifyAllMore
    bs
    (reactify p >> reactKword KwImp >> reactify q)
  reactifyAll bs (DALL s (DL (x ::. t))) = reactifyAll
      (bs >>
       reactBrackets Round (fromString x >> reactKword KwAsc >> reactify s))
      t
  reactifyAll bs (DALL s (DL (DK t))) = reactifyAll bs
      (DALL s (DL ("_" ::. t)))
  reactifyAll bs (DALL s t) = reactifyAllMore bs
    (reactKword KwAll >> reactify s >> reactify t)
  reactifyAll bs tm = reactifyAllMore bs (reactify tm)

  reactifyAllMore :: Pure React' -> Pure React' -> Pure React'
  reactifyAllMore bs d = div_ [ class_ "all-more" ] $
      bs >> reactKword KwImp >> d

> reactifyPair :: DInTmRN -> TermReact
> reactifyPair p = reactBrackets Square $ reactifyPairMore "" p

> reactifyPairMore :: TermReact -> DInTmRN -> TermReact
> reactifyPairMore d DVOID        = d
> reactifyPairMore d (DPAIR a b)  = reactifyPairMore
>     (d >> reactify a)
>     b
> reactifyPairMore d t            = d >> reactKword KwComma >> reactify t

> reactifySigma :: TermReact -> DInTmRN -> TermReact
> reactifySigma d DUNIT                      = reactifySigmaDone d ""
> reactifySigma d (DSIGMA s (DL (x ::. t)))  = reactifySigma
>     (d >> fromString x >> reactKword KwAsc >> reactify s >> reactKword KwSemi)
>     t
> reactifySigma d (DSIGMA s (DL (DK t)))     = reactifySigma
>     (d >> reactify s >> reactKword KwSemi) t
> reactifySigma d (DSIGMA s t) = reactifySigmaDone d
>     (reactKword KwSig >> reactify s >> reactify t)
> reactifySigma d t = reactifySigmaDone d (reactify t)

> reactifySigmaDone :: TermReact -> TermReact -> TermReact
> reactifySigmaDone s t = div_ [ class_ "sigma-done" ] $
>     reactKword KwSig >> reactBrackets Round (s >> t)

The `Elim` functor is straightforward.

> instance Reactive (Elim DInTmRN) where
>     reactify elim = div_ [ class_ "elim-dintmrn" ] $ reactify' elim where
>         reactify' (A t)  = reactify t
>         reactify' Out    = reactKword KwOut
>         reactify' (Call _) = reactKword KwCall
>         reactify' elim   = fromString $ show elim

> reactHere :: (TY :>: INTM) -> ProofState TermReact
> reactHere tt = do
>     dtm :=>: _ <- distillHere tt
>     return $ reactify dtm
