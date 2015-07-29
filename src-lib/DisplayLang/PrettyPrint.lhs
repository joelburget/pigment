<a name="DisplayLang.PrettyPrint">Pretty-printing</a>
===============

> {-# LANGUAGE ScopedTypeVariables, GADTs, FlexibleInstances, TypeOperators,
>     TypeSynonymInstances, PatternSynonyms, DeriveGeneric #-}

> module DisplayLang.PrettyPrint where

> import Data.Functor.Identity
> import Data.List
> import GHC.Generics
> import Text.PrettyPrint.HughesPJ

> import ProofState.Structure.Developments
> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.Scheme
> import Evidences.Tm
> import Kit.BwdFwd
> import Kit.MissingLibrary hiding ((<>))


TODO this Keyword business doesn't belong here

> data Keyword
>     = KwAsc
>     | KwComma
>     | KwSemi
>     | KwDefn
>     | KwUnderscore
>     | KwEq
>     | KwBy
>     | KwSet
>     | KwPi
>     | KwLambda
>     | KwCon
>     | KwOut

Equality

>     | KwEqBlue

Labelled Types

>     | KwCall
>     | KwLabel
>     | KwLabelEnd
>     | KwRet

Prob

>     | KwProb
>     | KwProbLabel
>     | KwPatPi
>     | KwSch
>     | KwSchTy
>     | KwExpPi
>     | KwImpPi

Prop

>     | KwProp
>     | KwAbsurd
>     | KwTrivial
>     | KwPrf
>     | KwAnd
>     | KwArr
>     | KwImp
>     | KwAll
>     | KwInh
>     | KwWit

Quotients

>     | KwQuotient

Records

>     | KwRecord
>     | KwRSig
>     | KwREmpty
>     | KwRCons

Sigma

>     | KwFst
>     | KwSnd
>     | KwSig

UId

>     | KwUId
>     | KwTag

>   deriving (Bounded, Enum, Eq, Show, Generic)

...and they look like this:

> key :: Keyword -> String

> key KwAsc        = ":"
> key KwComma      = ","
> key KwSemi       = ";"
> key KwDefn       = ":="
> key KwUnderscore = "_"
> key KwEq         = "="
> key KwBy         = "<="

> key KwSet        = "Set"
> key KwPi         = "Pi"
> key KwLambda     = "\\"

> key KwCon        = "con"
> key KwOut        = "%"

Equality

> key KwEqBlue     = "=="

Labelled Types

> key KwCall       = "call"
> key KwLabel      = "<"
> key KwLabelEnd   = ">"
> key KwRet        = "return"  -- rename me

Prob

> key KwProb       = "Prob"
> key KwProbLabel  = "ProbLabel"
> key KwPatPi      = "PatPi"
> key KwSch        = "Sch"
> key KwSchTy      = "SchTy"
> key KwExpPi      = "ExpPi"
> key KwImpPi      = "ImpPi"

Prop

> key KwProp       = "Prop"
> key KwAbsurd     = "FF"
> key KwTrivial    = "TT"
> key KwPrf        = ":-"
> key KwAnd        = "&&"
> key KwArr        = "->"
> key KwImp        = "=>"
> key KwAll        = "All"
> key KwInh        = "Inh"
> key KwWit        = "wit"

Quotients

> key KwQuotient   = "Quotient"

Records

> key KwRecord     = "Rec"
> key KwRSig       = "RSig"
> key KwREmpty     = "REmpty"
> key KwRCons      = "RCons"

Sigma

> key KwFst        = "!"
> key KwSnd        = "-"
> key KwSig        = "Sig"

UId

> key KwUId        = "UId"
> key KwTag        = "'"

    key k = error ("key: missing keyword " ++ show k)

It is straightforward to make a translation table, `keywords`:

> keywords :: [(String, Keyword)]
> keywords = map (\k -> (key k, k)) (enumFromTo minBound maxBound)


We use the `HughesPJ` pretty-printing combinators. This section defines
how to pretty-print everything defined in the Core chapter, and provides
she aspects to allow features to add their own pretty-printing support.

The `kword` function gives the document representing a `Keyword`.

> kword :: Keyword -> Doc
> kword = text . key

The `Pretty` class describes things that can be pretty-printed. The
`pretty` function takes a value `x` and the `Size` at which it should be
printed, and should return a document representation of `x`.

> class Show x => Pretty x where
>     pretty :: x -> Size -> Doc

The `wrapDoc` operator takes a document, its size and the size it should
be printed at. If the document's size is larger than the current size,
it is wrapped in parentheses.

> wrapDoc :: Doc -> Size -> Size -> Doc
> wrapDoc d dSize curSize
>   | dSize > curSize  = parens d
>   | otherwise        = d

When defining instances of `Pretty`, we will typically pattern-match on
the first argument and construct a function that takes the current size
by partially applying `wrapDoc` to a document and its size.

The `Can` functor is fairly easy to pretty-print, the only complexity
being with Pi types.

> instance Pretty (Can DInTmRN) where
>     pretty Set       = const (kword KwSet)
>     pretty (Pi s t)  = prettyPi empty (DPI s t)
>     pretty (Con x)   = wrapDoc (kword KwCon <> pretty x ArgSize) AppSize
>     pretty (EqBlue pp qq) = pretty (DEqBlue (foo pp) (foo qq))
>       where
>         foo :: (DInTmRN :>: DInTmRN) -> DExTmRN
>         foo (_    :>: DN x  ) = x
>         foo (xty  :>: x     ) = DType xty ::$ [A x]
>     pretty (Label l t) = const (kword KwLabel <>
>         pretty l maxBound <> kword KwAsc <> pretty t maxBound
>         <> kword KwLabelEnd)
>     pretty (LRet x) = wrapDoc (kword KwRet <> pretty x ArgSize) ArgSize
>     pretty Prop           = const (kword KwProp)
>     pretty (Prf p)        = wrapDoc (kword KwPrf <> pretty p AndSize) AppSize
>     pretty (All p q)      = prettyAll empty (DALL p q)
>     pretty (And p q)      = wrapDoc
>         (pretty p (pred AndSize) <> kword KwAnd <> pretty q AndSize)
>         AndSize
>     pretty Trivial        = const (kword KwTrivial)
>     pretty Absurd         = const (kword KwAbsurd)
>     pretty (Box (Irr p))  = pretty p
>     pretty (Inh ty)       = wrapDoc (kword KwInh <> pretty ty ArgSize) AppSize
>     pretty (Wit t)        = wrapDoc (kword KwWit <> pretty t ArgSize) AppSize
>     pretty (Quotient x r p) = wrapDoc
>         (sep [ kword KwQuotient
>              , nest 2 $ fsep $ map (`pretty` ArgSize) [x,r,p]
>              ])
>         ArgSize
>     pretty RSig              =  const $ text "RSignature"
>     pretty REmpty            =  const $ text "empty"
>     pretty (RCons s i t)     =  const $
>                                 pretty s ArgSize <> char '>'
>                                 <> pretty i ArgSize <> colon
>                                 <> pretty t ArgSize
>     pretty Unit         = wrapDoc (kword KwSig <> parens empty) AppSize
>     pretty Void         = prettyPair DVOID
>     pretty (Sigma s t)  = prettySigma empty (DSIGMA s t)
>     pretty (Pair a b)   = prettyPair (DPAIR a b)
>     pretty UId      = const (kword KwUId)
>     pretty (Tag s)  = const (kword KwTag <> text s)
>     pretty can       = const (quotes . text . show $ can)

The `prettyPi` function takes a document representing the domains so
far, a term and the current size. It accumulates domains until a
non(dependent) $\Pi$-type is found, then calls `prettyPiMore` to produce
the final document.

> prettyPi :: Doc -> DInTmRN -> Size -> Doc
> -- bs -> s -> t
> -- (cut off domains, show arrow)
> prettyPi bs (DPI s (DL (DK t))) = prettyPiMore bs
>     (pretty s (pred PiSize) <> kword KwArr <> pretty t PiSize)
> -- bs (x : s) (pretty t)
> -- (continue accumulating domains)
> prettyPi bs (DPI s (DL (x ::. t))) =
>     prettyPi (bs <> parens (text x <> kword KwAsc <> pretty s maxBound)) t
> -- bs -> pi s t
> -- (cut off domains, show pi)
> prettyPi bs (DPI s t) = prettyPiMore bs
>     (kword KwPi <> pretty s minBound <> pretty t minBound)
> -- bs -> (pretty tm)
> prettyPi bs tm = prettyPiMore bs (pretty tm PiSize)

The `prettyPiMore` function takes a bunch of domains (which may be
empty) and a codomain, and represents them appropriately for the current
size.

> prettyPiMore :: Doc -> Doc -> Size -> Doc
> prettyPiMore bs d
>   | isEmpty bs  = wrapDoc d PiSize
>   | otherwise   = wrapDoc (bs <> kword KwArr <> d) PiSize

The `Elim` functor is straightforward.

> instance Pretty (Elim DInTmRN) where
>     pretty (A t)  = pretty t
>     pretty Out    = const (kword KwOut)
>     pretty (Call _) = const (kword KwCall)
>     pretty Fst = const (kword KwFst)
>     pretty Snd = const (kword KwSnd)

To pretty-print a scope, we accumulate arguments until something other
than a $\lambda$-term is reached.

> instance Pretty DSCOPE where
>     pretty s = prettyLambda (B0 :< dScopeName s) (dScopeTm s)

> prettyLambda :: Bwd String -> DInTmRN -> Size -> Doc
> prettyLambda vs (DL s) = prettyLambda (vs :< dScopeName s) (dScopeTm s)
> prettyLambda vs tm = wrapDoc
>     (kword KwLambda <> text (unwords (trail vs)) <> kword KwArr
>         <> pretty tm ArrSize)
>     ArrSize

> instance Pretty DInTmRN where
>     pretty (DL s)          = pretty s
>     pretty (DC c)          = pretty c
>     pretty (DN n)          = pretty n
>     pretty (DQ x)          = const (char '?' <> text x)
>     pretty DU              = const (kword KwUnderscore)
>     pretty (DEqBlue t u) = wrapDoc
>         (pretty t ArgSize <> kword KwEqBlue <> pretty u ArgSize)
>         ArgSize
>     pretty (DTAG s)     = const (kword KwTag <> text s)
>     pretty (DTag s xs)  = wrapDoc (kword KwTag <> text s
>         <> hsep (map (`pretty` ArgSize) xs)) AppSize
>     pretty indtm           = const (quotes . text . show $ indtm)

> instance Pretty DExTmRN where
>     pretty (n ::$ [])   = pretty n
>     pretty (n ::$ els)  = wrapDoc
>         (pretty n AppSize <> hsep (map (`pretty` ArgSize) els))
>         AppSize

> instance Pretty DHEAD where
>     pretty (DP x)       = const (text (showRelName x))
>     pretty (DType ty)   = const (parens (kword KwAsc <> pretty ty maxBound))
>     pretty (DTEx ex)    = const (quotes . text . show $ ex)

> instance Pretty (Scheme DInTmRN) where
>     pretty (SchType ty) = wrapDoc (kword KwAsc <> pretty ty maxBound) ArrSize
>     pretty (SchExplicitPi (x :<: schS) schT) = wrapDoc (
>         parens (text x <> pretty schS maxBound)
>             <> pretty schT maxBound
>         ) ArrSize
>     pretty (SchImplicitPi (x :<: s) schT) = wrapDoc (
>         braces (text x <> kword KwAsc <> pretty s maxBound)
>             <> pretty schT maxBound
>         ) ArrSize

> prettyAll :: Doc -> DInTmRN -> Size -> Doc
> prettyAll bs (DALL (DPRF p) (DL (DK q))) = prettyAllMore bs
>   (pretty p (pred PiSize) <> kword KwImp <> pretty q PiSize)
> prettyAll bs (DALL s (DL (x ::. t))) =
>   prettyAll (bs <> parens (text x <> kword KwAsc <> pretty s maxBound)) t
> prettyAll bs (DALL s (DL (DK t))) = prettyAll bs (DALL s (DL ("_" ::. t)))
> prettyAll bs (DALL s t) = prettyAllMore bs
>   (kword KwAll <> pretty s minBound <> pretty t minBound)
> prettyAll bs tm = prettyAllMore bs (pretty tm PiSize)

> prettyAllMore :: Doc -> Doc -> Size -> Doc
> prettyAllMore bs d
>   | isEmpty bs  = wrapDoc d PiSize
>   | otherwise   = wrapDoc (bs <> kword KwImp <> d) PiSize

> prettyPair :: DInTmRN -> Size -> Doc
> prettyPair p = const (brackets (prettyPairMore empty p))

> prettyPairMore :: Doc -> DInTmRN -> Doc
> prettyPairMore d DVOID        = d
> prettyPairMore d (DPAIR a b)  = prettyPairMore (d <> pretty a minBound) b
> prettyPairMore d t            = d <> kword KwComma <> pretty t maxBound

> prettySigma :: Doc -> DInTmRN -> Size -> Doc
> prettySigma d DUNIT                      = prettySigmaDone d empty
> prettySigma d (DSIGMA s (DL (x ::. t)))  = prettySigma
>     (d <> text x <> kword KwAsc <> pretty s maxBound <> kword KwSemi) t
> prettySigma d (DSIGMA s (DL (DK t)))     = prettySigma
>     (d <> pretty s maxBound <> kword KwSemi) t
> prettySigma d (DSIGMA s t) = prettySigmaDone d
>     (kword KwSig <> pretty s minBound <> pretty t minBound)
> prettySigma d t = prettySigmaDone d (pretty t maxBound)

> prettySigmaDone :: Doc -> Doc -> Size -> Doc
> prettySigmaDone s t
>   | isEmpty s  = wrapDoc t AppSize
>   | otherwise  = wrapDoc (kword KwSig <> parens (s <> t)) AppSize

The `prettyBKind` function pretty-prints a `ParamKind` if supplied with
a document representing its name and type.

> prettyBKind :: ParamKind -> Doc -> Doc
> prettyBKind ParamLam  d = kword KwLambda <> d <> kword KwArr
> prettyBKind ParamAll  d = kword KwLambda <> d <> kword KwImp
> prettyBKind ParamPi   d = parens d <> kword KwArr

The `renderHouseStyle` hook allows us to customise the document
rendering if necessary.

> renderHouseStyle :: Doc -> String
> renderHouseStyle = render
