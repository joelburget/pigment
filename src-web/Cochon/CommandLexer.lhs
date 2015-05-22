Cochon Command Lexer
====================

> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, DeriveGeneric,
> OverloadedStrings #-}

> module Cochon.CommandLexer where

> import Control.Applicative
> import Data.Functor
> import Data.Either
> import Data.Monoid
> import Data.String
> import qualified Data.Text as T
> import GHCJS.Marshal
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

> data CochonArg
>     = StrArg String
>     -- ^ Pair with TfName
>     | InArg DInTmRN
>     -- ^ Pair with TfInArg
>     | ExArg DExTmRN
>     -- ^ Pair with TfExArg
>     | SchemeArg (Scheme DInTmRN)
>     -- ^ Pair with TfScheme

>     | OptionalArg CochonArg -- XXX not used?
>     | NoCochonArg -- XXX not used?
>     -- ^ (both) Pair with TfOption
>     | ListArgs [ CochonArg ] -- XXX not used?

>     | LeftArg CochonArg -- XXX not used?
>     -- ^ Pair with TfAlternative
>     | RightArg CochonArg -- XXX not used?
>     -- ^ Pair with TfAlternative

>     | PairArgs CochonArg CochonArg -- XXX not used?
>     -- ^ Pair with TfSequence?
>     deriving Show


Describing the Format of a Command
----------------------------------

TODO
should be able to label pieces to replicate things like this:
"give - solve the goal with <term>"

TODO
How do we pull out the pieces of a command?

> data TacticFormat
>     -- Terminals first:
>     = TfName T.Text
>     -- ^ Pair with StrArg
>     | TfKeyword Keyword
>     -- ^ Thrown away
>     | TfPseudoKeyword T.Text
>     -- ^ hack until I can get the keyword situation worked out (thrown away)
>     | TfInArg T.Text (Maybe T.Text)
>     -- ^ Pair with InArg
>     | TfExArg T.Text (Maybe T.Text)
>     -- ^ Pair with ExArg
>     | TfScheme T.Text (Maybe T.Text)
>     -- ^ Pair with SchemeArg

>     | TfAlternative TacticFormat TacticFormat
>     -- ^ Pair with LeftArg / RightArg
>     | TfOption TacticFormat
>     -- ^ Pair with OptionalArg / NoCochonArg
>     | TfRepeatZero TacticFormat
>     -- | TfRepeatOne TacticFormat
>     -- ^ (both) Pair with ListArgs / PairArgs
>     | TfSequence [TacticFormat]
>     | TfBracketed Bracket TacticFormat
>     | TfSep TacticFormat Keyword
>     deriving Generic

> tfAscription :: TacticFormat
> tfAscription = TfSequence
>     [ TfInArg "" Nothing
>     , TfKeyword KwAsc
>     , TfInArg "" Nothing
>     ]

> instance ToJSRef TacticFormat where

> instance IsString TacticFormat where
>     fromString = TfPseudoKeyword . fromString

> -- XXX if we did the work to successfully parse a command we should use that
> -- parse
> matchTactic :: TacticFormat -> [Token] -> Bool
> matchTactic fmt tokens = isRight (parse (parseTactic fmt) tokens)

> parseTactic :: TacticFormat -> Parsley Token (Bwd CochonArg)
> parseTactic (TfName _) = (B0 :<) <$> tokenString
> parseTactic (TfKeyword kw) = keyword kw $> B0
> parseTactic (TfPseudoKeyword str) = B0 <$ tokenEq (Identifier (T.unpack str))
> parseTactic (TfInArg _ _) = (B0 :<) <$> tokenInTm
> parseTactic (TfExArg _ _) = (B0 :<) <$> tokenExTm
> parseTactic (TfScheme _ _) = (B0 :<) <$> tokenScheme

> parseTactic (TfAlternative l r) = parseTactic l <|> parseTactic r
> parseTactic (TfOption fmt) = parseTactic fmt <|> empty

> parseTactic (TfRepeatZero format) = mconcat <$> some (parseTactic format)
> parseTactic (TfSequence formats) = foldr (>>) empty $ map parseTactic formats
> parseTactic (TfBracketed bTy format) = bracket bTy (parseTactic format)
> parseTactic (TfSep format kwd) =
>     mconcat <$> pSep (keyword kwd) (parseTactic format)


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

> tokenExTm :: Parsley Token CochonArg
> tokenExTm = ExArg <$> pDExTm

> tokenAscription :: Parsley Token CochonArg
> tokenAscription = ExArg <$> pAscriptionTC

> tokenInTm :: Parsley Token CochonArg
> tokenInTm = InArg <$> pDInTm

> tokenAppInTm :: Parsley Token CochonArg
> tokenAppInTm = InArg <$> sizedDInTm AppSize

> tokenName :: Parsley Token CochonArg
> tokenName = (ExArg . (::$ []) . DP) <$> nameParse

> tokenString :: Parsley Token CochonArg
> tokenString = StrArg <$> ident

> tokenScheme :: Parsley Token CochonArg
> tokenScheme = SchemeArg <$> pScheme

> tokenOption :: Parsley Token CochonArg -> Parsley Token CochonArg
> tokenOption p = (OptionalArg <$> bracket Square p) <|> pure NoCochonArg

tokenEither :: Parsley Token CochonArg -> Parsley Token CochonArg
                                       -> Parsley Token CochonArg
tokenEither p q = (LeftArg <$> p) <|> (RightArg <$> q)

> tokenListArgs :: Parsley Token CochonArg
>               -> Parsley Token ()
>               -> Parsley Token CochonArg
> tokenListArgs p sep = ListArgs <$> pSep sep p

> tokenPairArgs :: Parsley Token CochonArg -> Parsley Token () ->
>                  Parsley Token CochonArg -> Parsley Token CochonArg
> tokenPairArgs p sep q = PairArgs <$> p <* sep <*> q


Printers
--------

> argToStr :: CochonArg -> String
> argToStr (StrArg s) = s

> argToIn :: CochonArg -> DInTmRN
> argToIn (InArg a) = a

> argToEx :: CochonArg -> DExTmRN
> argToEx (ExArg a) = a

> argOption :: (CochonArg -> a) -> CochonArg -> Maybe a
> argOption p (OptionalArg x) = Just $ p x
> argOption _ NoCochonArg = Nothing

> argList :: (CochonArg -> a) -> CochonArg -> [a]
> argList f (ListArgs as) = map f as

argEither :: (CochonArg -> a) -> (CochonArg -> a) -> CochonArg -> a
argEither f g (LeftArg a) = f a
argEither f g (RightArg b) = g b

> argPair :: (CochonArg -> a) -> (CochonArg -> b) -> CochonArg -> (a, b)
> argPair f g (PairArgs a b) = (f a, g b)


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
>     { command :: TacticFormat
>     -- TODO
>     }

data CochonArg
    = StrArg String
    -- ^ Pair with TfName
    | InArg DInTmRN
    -- ^ Pair with TfInArg
    | ExArg DExTmRN
    -- ^ Pair with TfExArg
    | SchemeArg (Scheme DInTmRN)
    -- ^ Pair with TfScheme
    | OptionalArg CochonArg
    | NoCochonArg
    -- ^ (both) Pair with TfOption
    | ListArgs [ CochonArg ]

    | LeftArg CochonArg
    -- ^ Pair with TfAlternative
    | RightArg CochonArg
    -- ^ Pair with TfAlternative

    | PairArgs CochonArg CochonArg
