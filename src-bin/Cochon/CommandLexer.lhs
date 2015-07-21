Cochon Command Lexer
====================

> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, DeriveGeneric,
> OverloadedStrings, FlexibleInstances, CPP #-}

> module Cochon.CommandLexer where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Writer
> import Data.Functor
> import Data.Either
> import Data.Monoid
> import Data.Ord
> import Data.String
> import qualified Data.Text as T
> import Data.Text (Text)
> import GHC.Generics

> import Kit.BwdFwd
> import Kit.Parsley
> import DisplayLang.Lexer
> import DisplayLang.TmParse
> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.Scheme
> import ProofState.Edition.ProofContext

> import Debug.Trace


> -- The help for a tactic is:
> -- * a template showing the syntax of the command
> -- * an example use
> -- * a summary of what the command does
> -- * help for each individual argument (yes, they're named)

> data TacticHelp = TacticHelp
>     { template :: Text -- TODO highlight each piece individually
>     , example :: Text
>     , summary :: Text
>
>     -- maps from the name of the arg to its help
>     -- this is not a map because it's ordered
>     , argHelp :: [(Text, Text)]
>     }

> data Historic = Historic | Forgotten

> type Cmd a = WriterT String (State (Bwd ProofContext)) a

> setCtx :: Bwd ProofContext -> Cmd ()
> setCtx = put

> getCtx :: Cmd (Bwd ProofContext)
> getCtx = get



> -- A Cochon tactic consists of:
> --
> -- * `ctName` - the name of this tactic
> -- * `ctDesc` - high level description of the functionality
> -- * `ctFormat` - description of the command format for both parsing and
> --   contextual help
> -- * `ctParse` - parser that parses the arguments for this tactic
> -- * `ctxTrans` - state transition to perform for a given list of arguments and
> --     current context
> -- * `ctHelp` - help text for this tactic

> data CochonTactic = CochonTactic
>     { ctName    :: Text
>     , ctMessage :: Text
>     , ctDesc    :: TacticDescription
>     , ctxTrans  :: TacticResult -> Cmd ()
>     -- TODO(joel) - remove
>     , ctHelp    :: TacticHelp
>     } deriving Generic

> instance Show CochonTactic where
>     show = T.unpack . ctName

> instance Eq CochonTactic where
>     ct1 == ct2 = ctName ct1 == ctName ct2

> instance Ord CochonTactic where
>     compare = comparing ctName


> type CTData = (CochonTactic, TacticResult)


Tokens
------

Because Cochon tactics can take different types of arguments, we need a
tagging mechanism to distinguish them, together with projection
functions.

> data TacticResult
>     = TrName T.Text
>     -- ^ Pair with TfName
>     | TrKeyword
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
>     deriving Show


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
>     | TfInlineSequence [TacticFormat f a]
>     | TfBlockSequence [TacticFormat f a]
>     | TfBracketed Bracket (TacticFormat f a)
>     | TfSep (TacticFormat f a) Keyword
>     deriving Generic

pAscriptionTC = typeAnnot <$> pDInTm <* keyword KwAsc <*> pDInTm
  where typeAnnot tm ty = DType ty ::$ [A tm]

> tfAscription :: TacticDescription
> tfAscription = TfInlineSequence
>     [ TfInArg "term" Nothing
>     , TfKeyword KwAsc
>     , TfInArg "type" Nothing
>     ]

> -- XXX if we did the work to successfully parse a command we should use that
> -- parse
> matchTactic :: TacticDescription -> [Token] -> Bool
> matchTactic fmt tokens = isRight (parse (parseTactic fmt) tokens)

> parseTactic :: TacticDescription -> Parsley Token TacticResult
> parseTactic (TfName _) = trace "TfName" tokenString
> parseTactic (TfKeyword kw) = trace "TfKeyword" $ keyword kw $> TrKeyword
> parseTactic (TfInArg _ _) = trace "TfInArg" tokenInTm
> parseTactic (TfExArg _ _) = trace "TfExArg" tokenExTm
> parseTactic (TfScheme _ _) = trace "TfScheme" tokenScheme

> -- XXX parseTactic (TfAlternative l r) = parseTactic l <|> parseTactic r
> parseTactic (TfOption fmt) = trace "TfOption" $ parseTactic fmt <|> empty

> parseTactic (TfRepeatZero format) = trace "TfRepeatZero" $ TrRepeatZero <$> some (parseTactic format)
> parseTactic (TfBlockSequence formats) = trace "TfBlockSequence" $ TrSequence <$> sequence (map parseTactic formats)
> parseTactic (TfInlineSequence formats) = trace "TfInlineSequence" $ TrSequence <$> sequence (map parseTactic formats)
> parseTactic (TfBracketed bTy format) = trace "TfBracketed" $ bracket bTy (parseTactic format)
> parseTactic (TfSep format kwd) = trace "TfSep" $
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

> argToStr :: TacticResult -> T.Text
> argToStr (TrName s) = s

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
