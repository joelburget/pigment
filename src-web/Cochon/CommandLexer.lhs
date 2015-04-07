Cochon Command Lexer
====================

> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, DeriveGeneric,
> OverloadedStrings, FlexibleInstances #-}

> module Cochon.CommandLexer where

> import Control.Applicative
> import Data.Functor
> import Data.Either
> import Data.Monoid
> import Data.String
> import qualified Data.Text as T
> import GHCJS.Foreign
> import GHCJS.Marshal
> import GHCJS.Types
> import GHC.Generics

> import Kit.BwdFwd
> import Kit.Parsley
> import DisplayLang.Lexer
> import DisplayLang.TmParse
> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.Scheme


Tokens
------

Because Cochon tactics can take different types of arguments, we need a
tagging mechanism to distinguish them, together with projection
functions.

> data TacticResult
>     = TrName T.Text
>     -- ^ Pair with TfName
>     | TrKeyword
>     | TrPseudoKeyword
>     | TrInArg DInTmRN
>     -- ^ Pair with TfInArg
>     | TrExArg DExTmRN
>     -- r Pair with TfExArg
>     | TrScheme (Scheme DInTmRN)
>     -- ^ Pair with TfScheme

>     | TrAlternative (Either TacticResult TacticResult)
>     | TrOption (Maybe TacticResult)
>     | TrRepeatZero [TacticResult]
>     | TrSequence [TacticResult]
>     | TrBracketed Bracket TacticResult
>     | TrSep [TacticResult]


Describing the Format of a Command
----------------------------------

TODO
should be able to label pieces to replicate things like this:
"give - solve the goal with <term>"

TODO
How do we pull out the pieces of a command?

> type TacticDescription = TacticFormat (,) T.Text
> -- type TacticResult = TacticFormat Either (Maybe T.Text)

> data TacticFormat f a
>     -- Terminals first:
>     = TfName a
>     -- ^ Pair with StrArg
>     | TfKeyword Keyword
>     -- ^ Thrown away
>     | TfPseudoKeyword a
>     -- ^ hack until I can get the keyword situation worked out (thrown away)
>     | TfInArg a (Maybe T.Text)
>     -- ^ Pair with InArg
>     | TfExArg a (Maybe T.Text)
>     -- ^ Pair with ExArg
>     | TfScheme a (Maybe T.Text)
>     -- ^ Pair with SchemeArg

>     -- Now nonterminals
>     | TfAlternative (f (TacticFormat f a) (TacticFormat f a))
>     -- ^ Pair with LeftArg / RightArg
>     | TfOption (TacticFormat f a) -- TODO(joel) should be maybe?
>     -- ^ Pair with TrOption
>     | TfRepeatZero (TacticFormat f a) -- TODO(joel) - should be list?
>     -- | TfRepeatOne (TacticFormat f a)
>     -- ^ (both) Pair with ListArgs / PairArgs
>     | TfSequence [TacticFormat f a]
>     | TfBracketed Bracket (TacticFormat f a)
>     | TfSep (TacticFormat f a) Keyword
>     deriving Generic

pAscriptionTC = typeAnnot <$> pDInTm <* keyword KwAsc <*> pDInTm
  where typeAnnot tm ty = DType ty ::$ [A tm]

> tfAscription :: TacticDescription
> tfAscription = TfSequence
>     [ TfInArg "term" Nothing
>     , TfKeyword KwAsc
>     , TfInArg "type" Nothing
>     ]

> instance ToJSRef TacticDescription where

> instance (ToJSRef a, ToJSRef b) => ToJSRef (Either a b) where
>     toJSRef (Left a) = do
>         obj <- newObj
>         a' <- toJSRef a
>         let propName :: JSString
>             propName = "left"
>         setProp propName a' obj
>         return obj
>
>     toJSRef (Right b) = do
>         obj <- newObj
>         b' <- toJSRef b
>         let propName :: JSString
>             propName = "right"
>         setProp propName b' obj
>         return obj

> instance IsString TacticDescription where
>     fromString = TfPseudoKeyword . fromString

> -- XXX if we did the work to successfully parse a command we should use that
> -- parse
> matchTactic :: TacticDescription -> [Token] -> Bool
> matchTactic fmt tokens = isRight (parse (parseTactic fmt) tokens)

> parseTactic :: TacticDescription -> Parsley Token TacticResult
> parseTactic (TfName _) = tokenString
> parseTactic (TfKeyword kw) = keyword kw $> TrKeyword
> parseTactic (TfPseudoKeyword str) = TrPseudoKeyword <$ tokenEq (Identifier (T.unpack str))
> parseTactic (TfInArg _ _) = tokenInTm
> parseTactic (TfExArg _ _) = tokenExTm
> parseTactic (TfScheme _ _) = tokenScheme

> -- XXX parseTactic (TfAlternative l r) = parseTactic l <|> parseTactic r
> parseTactic (TfOption fmt) = parseTactic fmt <|> empty

> parseTactic (TfRepeatZero format) = TrRepeatZero <$> some (parseTactic format)
> parseTactic (TfSequence formats) = foldr (>>) empty $ map parseTactic formats
> parseTactic (TfBracketed bTy format) = bracket bTy (parseTactic format)
> parseTactic (TfSep format kwd) =
>     TrSep <$> pSep (keyword kwd) (parseTactic format)


Handling Tactics (sketch)
-------------------------

We need to be able to manipulate any part of the environment in response to a
tactic. Let's define a mini language of the kinds of things might need to do.

1. Show an error (or success!) message.
2. Some ProofState action?

I'd like to clarify what exactly a ProofState action can be.

1. An error (or success!) message
2. An external action? (kicking off a request)
3. Modify the current development (this is nebulous - creating and solving
   goals, building data, moving around in the development)


Tokenizer combinators
---------------------

> tokenExTm :: Parsley Token TacticResult
> tokenExTm = TrExArg <$> pDExTm

> tokenAscription :: Parsley Token TacticResult
> tokenAscription = TrExArg <$> pAscriptionTC

> tokenInTm :: Parsley Token TacticResult
> tokenInTm = TrInArg <$> pDInTm

> tokenAppInTm :: Parsley Token TacticResult
> tokenAppInTm = TrInArg <$> sizedDInTm AppSize

> tokenName :: Parsley Token TacticResult
> tokenName = (TrExArg . (::$ []) . DP) <$> nameParse

> tokenString :: Parsley Token TacticResult
> tokenString = TrName . T.pack <$> ident

> tokenScheme :: Parsley Token TacticResult
> tokenScheme = TrScheme <$> pScheme

> tokenOption :: Parsley Token TacticResult -> Parsley Token TacticResult
> tokenOption p = undefined -- TrOption <$> bracket Square p

tokenEither :: Parsley Token TacticResult -> Parsley Token TacticResult
                                          -> Parsley Token TacticResult
tokenEither p q = (TrAlternative . Left <$> p) <|> (TrAlternative . Right <$> q)

> tokenListArgs :: Parsley Token TacticResult
>               -> Parsley Token ()
>               -> Parsley Token TacticResult
> tokenListArgs p sep = TrSequence <$> pSep sep p

> tokenPairArgs :: Parsley Token TacticResult -> Parsley Token () ->
>                  Parsley Token TacticResult -> Parsley Token TacticResult
> tokenPairArgs p sep q = (\x y -> TrSequence [x, y]) <$> p <* sep <*> q


Printers
--------

> argToStr :: TacticResult -> String
> argToStr (TrName s) = T.unpack s

> argToIn :: TacticResult -> DInTmRN
> argToIn (TrInArg a) = a

> argToEx :: TacticResult -> DExTmRN
> argToEx (TrExArg a) = a

> argOption :: (TacticResult -> a) -> TacticResult -> Maybe a
> argOption p (TrOption (Just x)) = Just $ p x
> argOption _ _ = Nothing

> argList :: (TacticResult -> a) -> TacticResult -> [a]
> argList f (TrSequence as) = map f as

argEither :: (TacticResult -> a) -> (TacticResult -> a) -> TacticResult -> a
argEither f g (LeftArg a) = f a
argEither f g (RightArg b) = g b

> argPair :: (TacticResult -> a) -> (TacticResult -> b) -> TacticResult -> (a, b)
> argPair f g (TrSequence [a, b]) = (f a, g b)


User-Facing
-----------

The tricky bit:
* Showing the user the list of matching commands
* Giving contextual help for the command they're on

To display contextual help we need to know:
* The command
* Which part of the command the user's on

How *sick* would it be to show possible completions from the current scope?

> data ContextualHelpState = ContextualHelpState
>     { command :: TacticDescription
>     -- TODO
>     }
