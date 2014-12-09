\section{Pretty-printing}
\label{sec:DisplayLang.Reactify}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE ScopedTypeVariables, GADTs, FlexibleInstances, TypeOperators,
>     TypeSynonymInstances, OverloadedStrings #-}

> module DisplayLang.Reactify where

> import Data.List
> import Data.String (fromString)

import Text.PrettyPrint.HughesPJ

> import ProofState.Structure.Developments

> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.Scheme
> import DisplayLang.Lexer

> import Features.Features ()

> import Evidences.Tm

> import Kit.BwdFwd
> import Kit.MissingLibrary hiding ((<+>))

> import React hiding (key)

%endif

The |reactKword| function gives a react element representing a |Keyword|.

> reactKword :: Keyword -> PureReact
> reactKword = fromString . key

> parens :: PureReact -> PureReact
> parens r = "(" >> r >> ")"

The |Reactive| class describes things that can be made into React elements.

> class Reactive x where
>     reactify :: x -> PureReact

> instance Reactive (Can DInTmRN) where
>     reactify Set       = reactKword KwSet
>     reactify (Pi s t)  = reactPi "" (DPI s t)
>     reactify (Con x)   = reactKword KwCon >> reactify x
>     reactify (Anchor (DTAG u) t ts) = text_ u >> reactive ts
>     reactify AllowedEpsilon = ""
>     reactify (AllowedCons _ _ _ s ts) = reactive s >> reactive ts
>     reactify (Mu (Just l   :?=: _)) = reactify l
>     reactify (Mu (Nothing  :?=: Id t)) = reactKword KwMu >> reactify t
>     reactify (EnumT t)  = reactKword KwEnum >> reactify t
>     reactify Ze         = "0"
>     reactify (Su t)     = reactifyEnumIndex 1 t
>     reactify (EqBlue pp qq) = reactify (DEqBlue (foo pp) (foo qq))
>       where
>         foo :: (DInTmRN :>: DInTmRN) -> DExTmRN
>         foo (_    :>: DN x  ) = x
>         foo (xty  :>: x     ) = DType xty ::$ [A x]
>     reactify (Monad d x)   = reactKword KwMonad >> reactify d >> reactify x
>     reactify (Return x)    = reactKword KwReturn >> reactify x
>     reactify (Composite x) = reactKword KwCon >> reactify x
>     reactify (IMu (Just l   :?=: _) i)  = reactify l >> reactify i
>     reactify (IMu (Nothing  :?=: (Id ii :& Id d)) i)  = do
>         reactKword KwIMu
>         reactify ii
>         reactify d
>         reactify i
>     reactify (Label l t) = do
>         reactKword KwLabel
>         reactify l
>         reactKword KwAsc
>         reactify t
>         reactKword KwLabelEnd
>     reactify (LRet x) = reactKword KwRet >> reactify x
>     reactify (Nu (Just l :?=: _))  = reactify l
>     reactify (Nu (Nothing :?=: Id t))  = reactKword KwNu >> reactify t
>     reactify (CoIt d sty f s) = do
>         reactKword KwCoIt
>         reactify sty
>         reactify f
>         reactify s
>     reactify Prop           = reactKword KwProp
>     reactify (Prf p)        = reactKword KwPrf >> reactify p
>     reactify (All p q)      = reactifyAll empty (DALL p q)
>     reactify (And p q)      = reactify p >> reactKword KwAnd >> reactify q
>     reactify Trivial        = reactKword KwTrivial
>     reactify Absurd         = reactKword KwAbsurd
>     reactify (Box (Irr p))  = reactify p
>     reactify (Inh ty)       = reactKword KwInh >> reactify ty
>     reactify (Wit t)        = reactKword KwWit >> reactify t
>     reactify (Quotient x r p) = do
>         reactKword KwQuotient
>         mapM_ reactify [x,r,p]
>     reactify RSig              =  "RSignature"
>     reactify REmpty            =  "empty"
>     reactify (RCons s i t)     = do
>         reactify s
>         ">"
>         reactify i ArgSize
>         " , "
>         reactify t ArgSize
>     reactify Unit         = reactKword KwSig >> "()"
>     reactify Void         = reactifyPair DVOID
>     reactify (Sigma s t)  = reactifySigma "" (DSIGMA s t)
>     reactify (Pair a b)   = reactifyPair (DPAIR a b)
>     reactify UId      = reactKword KwUId
>     reactify (Tag s)  = reactKword KwTag >> fromString s
>     reactify can       = fromString . show $ can

The |reactPi| function takes a term and the current size. It accumulates
domains until a non(dependent) $\Pi$-type is found, then calls |reactPiMore|
to produce the final element.

> reactPi :: PureReact -> DInTmRN -> PureReact
> reactPi bs (DPI s (DL (DK t))) = reactPiMore bs
>     -- (reactify s >> reactKword KwArr >> reactify t) XXX
>     (reactKword KwArr)
> reactPi bs (DPI s (DL (x ::. t))) =
>     -- reactPi (bs >> "(" >> (fromString x >> reactKword KwAsc >> reactify s) >> ")") t XXX
>     reactPi (bs >> "(" >> (fromString x >> reactKword KwAsc) >> ")") t
> reactPi bs (DPI s t) = reactPiMore bs
>     -- (reactKword KwPi >> reactify s >> reactify t) XXX
>     (reactKword KwPi)
> -- reactPi bs tm = reactPiMore bs (reactify tm) XXX
> reactPi bs tm = ""

The |reactPiMore| function takes a bunch of domains (which may be empty)
and a codomain, and represents them appropriately for the current size.

> reactPiMore :: PureReact -> PureReact -> PureReact
> reactPiMore bs d = bs >> reactKword KwArr >> d

-- >   | isEmpty bs  = wrapDoc d PiSize
-- >   | otherwise   = wrapDoc (bs >> reactKword KwArr >> d) PiSize



To reactify a scope, we accumulate arguments until something other
than a $\lambda$-term is reached.

> instance Reactive DSCOPE where
>     reactify s = reactLambda (B0 :< dScopeName s) (dScopeTm s)

> reactLambda :: Bwd String -> DInTmRN -> PureReact
> reactLambda vs (DL s) = reactLambda (vs :< dScopeName s) (dScopeTm s)
> reactLambda vs tm = do
>     reactKword KwLambda
>     fromString $ intercalate " " $ trail vs
>     reactKword KwArr
>     reactify tm


> instance Reactive DInTmRN where
>     reactify (DL s)          = reactify s
>     reactify (DC c)          = reactify c
>     reactify (DN n)          = reactify n
>     reactify (DQ x)          = fromString $ '?':x
>     reactify DU              = reactKword KwUnderscore
>     reactify (DEqBlue t u) = reactify t >> kword KwEqBlue >> reactify u
>     reactify (DIMu (Just s   :?=: _) _)  = reactify s
>     reactify (DIMu (Nothing  :?=: (Id ii :& Id d)) i)  = do
>         reactKword KwIMu
>         reactify ii
>         reactify d
>         reactify i

>     reactify indtm           = fromString $ show $ indtm


> instance Reactive DExTmRN where
>     reactify (n ::$ els)  = reactify n >> mapM_ reactify els

> instance Reactive DHEAD where
>     reactify (DP x)       = fromString (showRelName x)
>     reactify (DType ty)   = reactKword KwAsc >> reactify ty
>     reactify (DTEx ex)    = fromString $ show ex

> instance Reactive (Scheme DInTmRN) where
>     reactify (SchType ty) = reactKword KwAsc >> reactify ty
>     reactify (SchExplicitPi (x :<: schS) schT) = do
>         "(" >> fromString x >> reactify schS >> ")"
>         reactify schT
>     reactify (SchImplicitPi (x :<: s) schT) = do
>         "[" >> fromString x >> reactKword KwAsc >> reactify s >> "]"
>         reactify schT

> reactifyEnumIndex :: Int -> DInTmRN -> PureReact
> reactifyEnumIndex n DZE      = fromString $ show n
> reactifyEnumIndex n (DSU t)  = reactifyEnumIndex (succ n) t
> reactifyEnumIndex n tm       = do
>     (fromString (show n))
>     reactKword KwPlus
>     reactify tm

> reactifyAll :: PureReact -> DInTmRN -> PureReact
> reactifyAll bs (DALL (DPRF p) (DL (DK q))) = reactifyAllMore
>   bs
>   (reactify p >> reactKword KwImp >> reactify q)
> reactifyAll bs (DALL s (DL (x ::. t))) = reactifyAll
>     (bs >> parens (fromString x >> reactKword KwAsc >> reactify s))
>     t
> reactifyAll bs (DALL s (DL (DK t))) = reactifyAll bs
>     (DALL s (DL ("_" ::. t)))
> reactifyAll bs (DALL s t) = reactifyAllMore bs
>   (reactKword KwAll >> reactify s >> reactify t)
> reactifyAll bs tm = reactifyAllMore bs (reactify tm)
>
> -- reactifyAllMore :: PureReact -> PureReact -> PureReact
> -- reactifyAllMore bs d
> --   | isEmpty bs  = wrapDoc d PiSize
> --   | otherwise   = wrapDoc (bs <+> kword KwImp <+> d) PiSize
>
> reactifyAllMore :: PureReact -> PureReact -> PureReact
> reactifyAllMore bs d = bs >> reactKword KwImp >> d

> reactifyPair :: DInTmRN -> PureReact
> reactifyPair p = "[" >> reactifyPairMore "" p >> "]"

> reactifyPairMore :: PureReact -> DInTmRN -> PureReact
> reactifyPairMore d DVOID        = d
> reactifyPairMore d (DPAIR a b)  = reactifyPairMore
>     (d >> reactify a)
>     b
> reactifyPairMore d t            = d >> reactKword KwComma >> reactify t

> reactifySigma :: PureReact -> DInTmRN -> PureReact
> reactifySigma d DUNIT                      = reactifySigmaDone d ""
> reactifySigma d (DSIGMA s (DL (x ::. t)))  = reactifySigma
>     (d >> fromString x >> reactKword KwAsc >> reactify s >> reactKword KwSemi)
>     t
> reactifySigma d (DSIGMA s (DL (DK t)))     = reactifySigma
>     (d >> reactify s >> reactKword KwSemi) t
> reactifySigma d (DSIGMA s t) = reactifySigmaDone d
>     (reactKword KwSig >> reactify s >> reactify t)
> reactifySigma d t = reactifySigmaDone d (reactify t)

> reactifySigmaDone :: PureReact -> PureReact -> PureReact
> reactifySigmaDone s t = reactKword KwSig >> "(" >> s >> t >> ")"

> -- reactifySigmaDone :: PureReact -> PureReact -> PureReact
> -- reactifySigmaDone s t
> --   | isEmpty s  = wrapDoc t AppSize
> --   | otherwise  = wrapDoc (kword KwSig <+> parens (s <+> t)) AppSize

The |Elim| functor is straightforward.

> instance Reactive (Elim DInTmRN) where
>     reactify (A t)  = reactify t
>     reactify Out    = reactKword KwOut)
>     reactify (Call _) = reactKword KwCall
>     reactify elim   = fromString $ show $ elim
