<a name="DisplayLang.TmParse">Parsing Terms</a>
=============

> {-# LANGUAGE TypeOperators, GADTs #-}

> module DisplayLang.TmParse where

> import Control.Applicative
> import Data.Char
> import Data.Maybe
> import Data.Foldable hiding (notElem, concatMap)

> import Kit.MissingLibrary
> import Kit.Parsley
> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.Scheme
> import DisplayLang.Lexer
> import Evidences.Tm

The term parser eats structured `Token`s as defined in @Lexer.lhs@. It
uses the monadic parser combinators to translate the grammar of terms
defined in Section [language](#language).

Names
-----

A relative name is a list of idents separated by dots, and possibly with
`^` or `_` symbols (for relative or absolute offsets).

> nameParse :: Parsley Token RelName
> nameParse = do
>     s <- ident
>     case parse pName s of
>         Right rn  -> return rn
>         Left e    -> fail "nameParse failed"

> pName :: Parsley Char RelName
> pName = (:) <$> pNamePart <*> many (tokenEq '.' *> pNamePart)

> pNamePart :: Parsley Char (String, Offs)
> pNamePart = ((,) <$> pNameWord <* tokenEq '^' <*> (Rel . read <$> pNameOffset))
>         <|> ((,) <$> pNameWord <* tokenEq '_' <*> (Abs . read <$> pNameOffset))
>         <|> ((,) <$> pNameWord <*> pure (Rel 0))

> pNameWord :: Parsley Char String
> pNameWord = some (tokenFilter (`notElem` "_^."))

> pNameOffset :: Parsley Char String
> pNameOffset = some (tokenFilter isDigit)

Overall parser structure
------------------------

The `pDExTm` and `pDInTm` functions start parsing at the maximum size.

> pDExTm :: Parsley Token DExTmRN
> pDExTm = sizedDExTm maxBound

> pDInTm :: Parsley Token DInTmRN
> pDInTm = sizedDInTm maxBound

We do not allow ascriptions in the term syntax, but they are useful in
commands, so we provide `pAscription` to parse an ascription into
separate components, and `pAscriptionTC` to parse an ascription as an
appropriate type annotation.

> pAscription :: Parsley Token (DInTmRN :<: DInTmRN)
> pAscription = (:<:) <$> pDInTm <* keyword KwAsc <*> pDInTm

> pAscriptionTC :: Parsley Token DExTmRN
> pAscriptionTC = typeAnnot <$> pDInTm <* keyword KwAsc <*> pDInTm
>   where typeAnnot tm ty = DType ty ::$ [A tm]

Each `sized` parser tries the appropriate `special` parser for the size,
then falls back to parsing at the previous size followed by a `more`
parser. At the smallest size, brackets must be used to start parsing
from the largest size again. Concrete syntax is matched using the lists
of parsers defined in the following subsection.

> sizedDExTm :: Size -> Parsley Token DExTmRN
> sizedDExTm z = ((::$ []) <$> specialHead z) <|>
>       (if z > minBound  then pLoop (sizedDExTm (pred z)) (moreDExTm z)
>                         else bracket Round pDExTm)

> sizedDInTm :: Size -> Parsley Token DInTmRN
> sizedDInTm z = specialDInTm z <|> ((DN . (::$ [])) <$> specialHead z) <|>
>       (if z > minBound  then pLoop (sizedDInTm (pred z)) (moreInEx z)
>                         else bracket Round pDInTm)

> specialHead :: Size -> Parsley Token DHEAD
> specialHead = sizeListParse headParsers

> specialDInTm :: Size -> Parsley Token DInTmRN
> specialDInTm = sizeListParse inDTmParsersSpecial

> moreInEx :: Size -> DInTmRN -> Parsley Token DInTmRN
> moreInEx z (DN e)  = (DN <$> moreDExTm z e) <|> moreDInTm z (DN e)
> moreInEx z t       = moreDInTm z t

> moreDExTm :: Size -> DExTmRN -> Parsley Token DExTmRN
> moreDExTm s e = (e $::$) <$> sizeListParse elimParsers s

> moreDInTm :: Size -> DInTmRN -> Parsley Token DInTmRN
> moreDInTm = paramListParse inDTmParsersMore

Lists of sized parsers
----------------------

A `SizedParserList` is a list of parsers associated to every size; a
`ParamParserList` allows the parser to depend on a parameter.

> type SizedParserList a    = [(Size, [Parsley Token a])]
> type ParamParserList a b  = [(Size, [a -> Parsley Token b])]

We can construct such a list from a list of size-parser pairs thus:

> arrange :: [(Size, b)] -> [(Size, [b])]
> arrange xs = map (\s -> (s,  pick s xs)) (enumFromTo minBound maxBound)
>   where
>     pick :: Eq a => a -> [(a, b)] -> [b]
>     pick x = concatMap (\(a , b) -> [b | a == x])

To parse using a list at a particular size, we try all the parsers at
that size in order:

> sizeListParse :: SizedParserList a -> Size -> Parsley Token a
> sizeListParse sps s = pTryList . fromJust $ lookup s sps

> paramListParse :: ParamParserList a b -> Size -> a -> Parsley Token b
> paramListParse sfs s a = pTryList . map ($ a) . fromJust $ lookup s sfs

> pTryList :: [Parsley Token a] -> Parsley Token a
> pTryList = asum

Now we define the lists of parsers that actually match bits of the
concrete syntax. Note that each list has a corresponding aspect so
features can extend the parser.

> headParsers :: SizedParserList DHEAD
> headParsers = arrange
>    [ (ArgSize, DType <$> bracket Round (keyword KwAsc *> pDInTm))
>    , (ArgSize, DP <$> nameParse)
>    ]

> elimParsers :: SizedParserList (Elim DInTmRN)
> elimParsers = arrange [
>     (AppSize, Call <$ keyword KwCall <*> pure DU),
>     (AppSize, Fst <$ keyword KwFst),
>     (AppSize, Snd <$ keyword KwSnd),
>     (AppSize, Out <$ keyword KwOut),
>     (AppSize, A <$> sizedDInTm ArgSize)
>     ]

> inDTmParsersSpecial :: SizedParserList DInTmRN
> inDTmParsersSpecial = arrange [
>     (AndSize, DMU Nothing <$ keyword KwMu <*> sizedDInTm ArgSize),
>     (ArgSize, mkNum <$> (read <$> digits)
>                     <*> optional (keyword KwPlus *> sizedDInTm ArgSize)),
>     (AndSize, DENUMT <$ keyword KwEnum <*> sizedDInTm ArgSize),
>     (ArgSize, DRETURN <$ keyword KwReturn <*> sizedDInTm ArgSize),
>     (AndSize, DMONAD <$  keyword KwMonad
>                      <*> sizedDInTm ArgSize
>                      <*> sizedDInTm ArgSize),
>     (AndSize, DIMU Nothing <$  keyword KwIMu
>                            <*> sizedDInTm ArgSize
>                            <*> sizedDInTm ArgSize
>                            <*> sizedDInTm ArgSize),
>     (ArgSize, DLABEL <$  keyword KwLabel
>                      <*> sizedDInTm AppSize
>                      <*  keyword KwAsc
>                      <*> sizedDInTm ArgSize
>                      <*  keyword KwLabelEnd),
>     (ArgSize, DLRET <$ keyword KwRet <*> sizedDInTm ArgSize),
>     (AndSize, DNU Nothing <$ keyword KwNu <*> sizedDInTm ArgSize),
>     (AndSize, DCOIT DU <$  keyword KwCoIt
>                        <*> sizedDInTm ArgSize
>                        <*> sizedDInTm ArgSize
>                        <*> sizedDInTm ArgSize),
>     (ArgSize, DPROP     <$ keyword KwProp),
>     (ArgSize, DABSURD   <$ keyword KwAbsurd),
>     (ArgSize, DTRIVIAL  <$ keyword KwTrivial),
>     (AndSize, DPRF <$ keyword KwPrf <*> sizedDInTm AndSize),
>     (AndSize, DINH <$ keyword KwInh <*> sizedDInTm ArgSize),
>     (AndSize, DWIT <$ keyword KwWit <*> sizedDInTm ArgSize),
>     (AndSize, DALL <$  keyword KwAll
>                    <*> sizedDInTm ArgSize
>                    <*> sizedDInTm ArgSize),
>     (AndSize, DQUOTIENT <$  keyword KwQuotient
>                         <*> sizedDInTm ArgSize
>                         <*> sizedDInTm ArgSize
>                         <*> sizedDInTm ArgSize),
>     (AndSize, DRECORD Nothing <$ keyword KwRecord <*> sizedDInTm ArgSize),
>     (ArgSize, DRSIG <$ keyword KwRSig),
>     (ArgSize, DREMPTY <$ keyword KwREmpty),
>     (ArgSize, DRCONS <$  keyword KwRCons
>                      <*> sizedDInTm ArgSize
>                      <*> sizedDInTm ArgSize
>                      <*> sizedDInTm ArgSize),
>     (ArgSize, bracket Square tuple),
>     (ArgSize, keyword KwSig *> bracket Round sigma),
>     (ArgSize, DSIGMA <$  keyword KwSig
>                      <*> sizedDInTm ArgSize
>                      <*> sizedDInTm ArgSize),
>     (ArgSize, DUID <$ keyword KwUId),
>     (ArgSize, DTAG <$ keyword KwTag <*> ident),
>     (AppSize, DTag <$ keyword KwTag
>                    <*> ident
>                    <*> many (sizedDInTm ArgSize)),
>     (ArgSize, DSET <$ keyword KwSet),
>     (ArgSize, DQ <$> pFilter questionFilter ident),
>     (ArgSize, DU <$ keyword KwUnderscore),
>     (ArgSize, DCON <$ keyword KwCon <*> sizedDInTm ArgSize),
>     (ArgSize, iter mkDLAV <$  keyword KwLambda
>                           <*> some (ident <|> underscore)
>                           <*  keyword KwArr
>                           <*> pDInTm),
>     (AndSize, DPI <$  keyword KwPi
>                   <*> sizedDInTm ArgSize
>                   <*> sizedDInTm ArgSize),
>     (PiSize, flip iter
>         <$> some (bracket Round
>             ((,) <$> (ident <|> underscore)
>                  <*  keyword KwAsc
>                  <*> pDInTm
>             ))
>         <*> ((uncurry mkDPIV  <$ keyword KwArr)
>          <|> (uncurry mkDALLV <$ keyword KwImp))
>         <*> pDInTm
>     )
>     ]

> inDTmParsersMore :: ParamParserList DInTmRN DInTmRN
> inDTmParsersMore = arrange [
>     (EqSize, \ t -> DEqBlue <$> (pFilter isEx (pure t) <* keyword KwEqBlue)
>                             <*> pFilter isEx (sizedDInTm (pred EqSize))),
>     (AndSize, \ s -> DAND s <$ keyword KwAnd <*> sizedDInTm AndSize),
>     (ArrSize, \ s -> DIMP s <$ keyword KwImp <*> sizedDInTm PiSize),
>     (ArrSize, \ s -> DARR s <$ keyword KwArr <*> sizedDInTm PiSize)
>     ]

Parser support code
-------------------

> mkNum :: Int -> Maybe DInTmRN -> DInTmRN
> mkNum 0 Nothing = DZE
> mkNum 0 (Just t) = t
> mkNum n t = DSU (mkNum (n-1) t)

> isEx :: DInTmRN -> Maybe DExTmRN
> isEx (DN tm)  = Just tm
> isEx _        = Nothing

> tuple :: Parsley Token DInTmRN
> tuple = (DPAIR <$> sizedDInTm ArgSize
>                <*> ((keyword KwComma *> pDInTm) <|> tuple))
>     <|> (DVOID <$ pEndOfStream)

> sigma :: Parsley Token DInTmRN
> sigma = (mkSigma <$> optional (ident <* keyword KwAsc)
>                  <*> pDInTm
>                  <*> sigmaMore)
>      <|> DUNIT <$ pEndOfStream

> sigmaMore :: Parsley Token DInTmRN
> sigmaMore = (keyword KwSemi *> (sigma <|> pDInTm))
>   <|> (mkSigma Nothing . DPRF <$ keyword KwPrf <*> pDInTm <*> sigmaMore)
>   <|> (DPRF <$ keyword KwPrf <*> pDInTm)

> mkSigma :: Maybe String -> DInTmRN -> DInTmRN -> DInTmRN
> mkSigma Nothing s t = DSIGMA s (DL (DK t))
> mkSigma (Just x) s t = DSIGMA s (DL (x ::. t))

> questionFilter :: String -> Maybe String
> questionFilter ('?':s)  = Just s
> questionFilter _        = Nothing

> underscore :: Parsley Token String
> underscore = keyword KwUnderscore >> pure "_"

> mkDLAV :: String -> DInTmRN -> DInTmRN
> mkDLAV "_"  t = DL (DK t)
> mkDLAV x    t = DLAV x t

> mkDPIV :: String -> DInTmRN -> DInTmRN -> DInTmRN
> mkDPIV   "_"  s t = DPI s (DL (DK t))
> mkDPIV   x    s t = DPIV x s t

> mkDALLV :: String -> DInTmRN -> DInTmRN -> DInTmRN
> mkDALLV  "_"  s p = DALL s (DL (DK p))
> mkDALLV  x    s p = DALLV x s p

Parsing schemes
---------------

> pScheme :: Parsley Token (Scheme DInTmRN)
> pScheme = mkScheme <$> many pSchemeBit <* keyword KwAsc <*> pDInTm
>   where
>     pSchemeBit :: Parsley Token (String, Either (Scheme DInTmRN) DInTmRN)
>     pSchemeBit = bracket Round ((,) <$> ident
>                                     <*  keyword KwAsc
>                                     <*> (Left . SchType <$> pDInTm))
>              <|> bracket Curly ((,) <$> ident
>                                     <*  keyword KwAsc
>                                     <*> (Right <$> pDInTm))
>     mkScheme :: [(String, Either (Scheme DInTmRN) DInTmRN)]
>              -> DInTmRN
>              -> Scheme DInTmRN
>     mkScheme [] ty = SchType ty
>     mkScheme ((x, Left s) : bits) ty =
>         SchExplicitPi (x :<: s) (mkScheme bits ty)
>     mkScheme ((x, Right s) : bits) ty =
>         SchImplicitPi (x :<: s) (mkScheme bits ty)
