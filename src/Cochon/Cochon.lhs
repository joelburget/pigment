\section{Cochon (Command-line Interface)}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs,
>     DeriveFunctor, DeriveFoldable, DeriveTraversable, OverloadedStrings,
>     CPP #-}

> module Cochon.Cochon where

> import Control.Applicative
> import Control.Monad.State
> import Control.Monad.Except
> import Data.Foldable as Foldable
> import Data.List hiding (find)
> import Data.Ord
> import Data.String
> import Data.Traversable

> import NameSupply.NameSupply

> import Evidences.Tm hiding (In)

> import DisplayLang.Lexer
> import DisplayLang.Name
> import DisplayLang.TmParse
> import DisplayLang.DisplayTm
> import DisplayLang.PrettyPrint

> import ProofState.Edition.ProofContext
> import ProofState.Edition.ProofState
> import ProofState.Edition.Entries
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation

> import ProofState.Interface.Search
> import ProofState.Interface.ProofKit
> import ProofState.Interface.Module
> import ProofState.Interface.NameResolution
> import ProofState.Interface.Solving
> import ProofState.Interface.Parameter

> import Tactics.Elimination
> import Tactics.PropositionSimplify
> import Tactics.ProblemSimplify
> import Tactics.Information
> import Tactics.Gadgets
> import Tactics.Data
> import Tactics.IData
> import Tactics.Relabel
> import Tactics.ShowHaskell
> import Tactics.Matching
> import Tactics.Unification

> import Elaboration.Elaborator
> import Elaboration.Scheduler

> import Distillation.Distiller

> import Cochon.CommandLexer
> import Cochon.Error

> import Compiler.Compiler

> import Kit.BwdFwd
> import Kit.Parsley
> import Kit.MissingLibrary

#ifdef __HASTE__
> import Haste hiding (fromString, prompt)
> import Haste.JSON
> import Haste.Prim
#endif
> import Prelude hiding (div)
> import Rascal hiding (key)
> import qualified Rascal

%endif

Here we have a very basic command-driven interface to the proof state monad.

Model
=====

> data InteractionState = InteractionState
>     { proofCtx :: Bwd ProofContext
>     , userInput :: String
>     , outputLog :: [ReactM ()]
>     -- XXX(joel) - should this be ProofState (ReactM ())?
>     , proofState :: ProofState String
>     , pageElem :: Elem
>     }

> data TransitionEvent
>     = TransitionChange String
>     | TransitionSpecial SpecialKey
>     deriving Show

> type CTData = (CochonTactic, [CochonArg])

Controller Helpers
==================

PageM

> newtype PageM a = PageM
>     (InteractionState -> (a, InteractionState))

> data SpecialKey
>     = Enter
>     deriving Show

> instance Monad PageM where
>     return a = PageM $ \state -> (a, state)
>     (PageM fa) >>= interact = PageM $ \state ->
>         let (a, state') = fa state
>             PageM fb = interact a
>         in fb state'

> unPageM :: PageM a -> InteractionState -> InteractionState
> unPageM (PageM f) = snd . f

> getProofState :: PageM (ProofState String)
> getProofState = PageM $ \state -> (proofState state, state)

> setProofState :: ProofState String -> PageM ()
> setProofState st = PageM $ \state -> ((), state{proofState=st})

> setCtx :: Bwd ProofContext -> PageM ()
> setCtx ctx = PageM $ \state -> ((), state{proofCtx=ctx})

> getInteractionState :: PageM InteractionState
> getInteractionState = PageM $ \state -> (state, state)

> setInteractionState :: InteractionState -> PageM ()
> setInteractionState state = PageM $ \_ -> ((), state)

> getCtx :: PageM (Bwd ProofContext)
> getCtx = PageM $ \state -> (proofCtx state, state)

> displayUser :: ReactM () -> PageM ()
> displayUser react =
>     let elem = div (ReactAttrs [("className", "log-elem")] []) react
>     in PageM $ \state -> ((), state{outputLog=elem:(outputLog state)})

> tellUser :: String -> PageM ()
> tellUser = displayUser . fromString

> resetUserInput :: PageM ()
> resetUserInput = PageM $ \state -> ((), state{userInput=""})

View
====

> showPage :: InteractionState -> IO ()
> -- TODO gross getting the elem each time
> -- add it to InteractionState
> showPage state = renderComponent (pageElem state) (page state)

> page :: InteractionState -> ReactM ()
> page state = div (ReactAttrs [("className", "page")] []) $ do
>     proofCtxDisplay (proofCtx state)
>     div (ReactAttrs [("className", "right-pane")] []) $ do
>         prompt (toJSStr (userInput state)) (inputHandler state)
>         interactionLog (outputLog state)
>     tacticList

> prompt :: JSString -> (TransitionEvent -> IO ()) -> ReactM ()
> prompt v handle = div (ReactAttrs [("className", "prompt")] []) $
>     input (ReactAttrs [("className", "prompt-input"), ("value", Str v)]
>                       [ onChange   (handle <#> handleChange)
>                       , onKeyPress (handle <#> handleKey)
>                       ])

> interactionLog :: [ReactM ()] -> ReactM ()
> interactionLog logs = div
>     (ReactAttrs [("className", "interaction-log")] [])
>     (Prelude.sequence_ logs)

> proofCtxDisplay :: Bwd ProofContext -> ReactM ()
> proofCtxDisplay (_ :< ctx) = div
>     (ReactAttrs [("className", "ctx-display")] [])
>     (pre (ReactAttrs [] []) $ fst $ runProofState prettyProofState ctx)

> tacticList :: ReactM ()
> tacticList = div
>     (ReactAttrs [("className", "tactic-list")] [])
>     (Foldable.forM_ cochonTactics $ \tactic -> div
>         (ReactAttrs [("className", "tactic-info")] []) (ctHelp tactic)
>     )

Controller
==========

We start out here. Main calls `cochon emptyContext`.

> cochon :: ProofContext -> IO ()
> cochon loc = do
>     Just e <- elemById "inject"
>     let pc = B0 :< loc
>         startState = InteractionState pc "" [] showPrompt e
>     validateDevelopment pc
>     showPage startState

PageM = (InteractionState -> (a, InteractionState))

> cochon' :: PageM ()
> cochon' = do
>     locs :< loc <- getCtx
>     pfSt <- getProofState
>     let (msg, state') = runProofState pfSt loc
>     tellUser msg

> inputHandler :: InteractionState -> TransitionEvent -> IO ()
> inputHandler state x@(TransitionChange str) = do
>     print x
>     showPage state{userInput=str}
> inputHandler state (TransitionSpecial Enter) = do
>     let action = case parseCmd (userInput state) of
>             Left err -> tellUser err
>             Right interaction -> do
>                 interaction
>                 locs :< loc <- getCtx
>                 pfSt <- getProofState
>                 let (msg, maybeCtx) = runProofState pfSt loc
>                 tellUser msg
>                 case maybeCtx of
>                     Just loc' -> do
>                         setCtx (locs :< loc')
>                         resetUserInput
>                     Nothing -> return ()
>     showPage (unPageM action state)

TODO refactor / rename this

> parseCmd :: String -> Either String (PageM ())
> parseCmd l = case parse tokenize l of
>     Left  pf -> Left ("Tokenize failure: " ++ describePFailure pf id)
>     Right ts -> case parse pCochonTactics ts of
>         Left pf -> Left $
>             "Parse failure: " ++
>             describePFailure pf (intercalate " " . map crushToken)
>         Right cds -> Right $ doCTactics cds

> (<#>) :: (TransitionEvent -> IO ())
>       -> (a -> Maybe TransitionEvent)
>       -> a
>       -> IO ()
> effect <#> handler = \a -> case handler a of
>     Just x -> effect x
>     Nothing -> return ()

> handleChange :: ChangeEvent -> Maybe TransitionEvent
> handleChange = Just . TransitionChange . fromJSStr . targetValue

> handleKey :: KeyboardEvent -> Maybe TransitionEvent
> handleKey evt = case fromJSStr (Rascal.key evt) of
>     "Enter" -> Just $ TransitionSpecial Enter
>     _ -> Nothing

> paranoid = False
> veryParanoid = False

XXX(joel) refactor this whole thing
  - remove putStrLn
  - make it PageM
  - fix line length
  - surely this can be expressed more compactly

> validateDevelopment :: Bwd ProofContext -> IO ()
> validateDevelopment locs@(_ :< loc) = if veryParanoid
>     then Foldable.mapM_ validateCtxt locs -- XXX: there must be a better way to do that
>     else if paranoid
>         then validateCtxt loc
>         else return ()
>   where validateCtxt loc =
>             case evalStateT (validateHere `catchError` catchUnprettyErrors) loc of
>               Left ss -> do
>                   putStrLn "*** Warning: definition failed to type-check! ***"
>                   putStrLn $ renderHouseStyle $ prettyStackError ss
>               _ -> return ()


> showPrompt :: ProofState String
> showPrompt = do
>     mty <- optional' getHoleGoal
>     case mty of
>         Just (_ :=>: ty)  -> (|(showGoal ty) ++ showInputLine|)
>         Nothing           -> showInputLine
>   where
>     showGoal :: TY -> ProofState String
>     showGoal ty@(LABEL _ _) = do
>         h <- infoHypotheses
>         s <- prettyHere . (SET :>:) =<< bquoteHere ty
>         return $ h ++ "\n" ++ "Programming: " ++ show s ++ "\n"
>     showGoal ty = do
>         s <- prettyHere . (SET :>:) =<< bquoteHere ty
>         return $ "Goal: " ++ show s ++ "\n"
>
>     showInputLine :: ProofState String
>     showInputLine = do
>         mn <- optional' getCurrentName
>         return $ case mn of
>             Just n   -> showName n ++ " > "
>             Nothing  -> "> "


> describePFailure :: PFailure a -> ([a] -> String) -> String
> describePFailure (PFailure (ts, fail)) f = (case fail of
>     Abort        -> "parser aborted."
>     EndOfStream  -> "end of stream."
>     EndOfParser  -> "end of parser."
>     Expect t     -> "expected " ++ f [t] ++ "."
>     Fail s       -> s
>   ) ++ (if length ts > 0
>        then "\nSuccessfully parsed: ``" ++ f ts ++ "''."
>        else "")


A Cochon tactic consists of:
\begin{description}
\item[|ctName|] the name of this tactic
\item[|ctParse|] a parser that parses the arguments for this tactic
\item[|ctxTrans|] a state transition to perform for a given list of arguments and current context
\item[|ctHelp|] the help text for this tactic
\end{description}

> data CochonTactic =
>     CochonTactic  {  ctName   :: String
>                   ,  ctParse  :: Parsley Token (Bwd CochonArg)
>                   ,  ctxTrans :: [CochonArg] -> PageM ()
>                   ,  ctHelp   :: ReactM ()
>                   }

> instance Show CochonTactic where
>     show = ctName

> instance Eq CochonTactic where
>     ct1 == ct2 =  ctName ct1 == ctName ct2

> instance Ord CochonTactic where
>     compare = comparing ctName


The |tacticsMatching| function identifies Cochon tactics that match the
given string, either exactly or as a prefix.

> tacticsMatching :: String -> [CochonTactic]
> tacticsMatching x = case find ((x ==) . ctName) cochonTactics of
>     Just ct  -> [ct]
>     Nothing  -> filter (isPrefixOf x . ctName) cochonTactics

> tacticNames :: [CochonTactic] -> String
> tacticNames = intercalate ", " . map ctName


Given a proof state command and a context, we can run the command with
|runProofState| to produce a message (either the response from the command or
the error message) and |Maybe| a new proof context.

> runProofState
>     :: ProofState String
>     -> ProofContext
>     -> (String, Maybe ProofContext)
> runProofState m loc =
>     case runStateT (m `catchError` catchUnprettyErrors) loc of
>         Right (s, loc') -> (s, Just loc')
>         Left ss         -> (renderHouseStyle $ prettyStackError ss, Nothing)


> simpleOutput :: ProofState String -> PageM ()
> simpleOutput eval = do
>     locs :< loc <- getCtx
>     case runProofState (eval <* startScheduler) loc of
>         (s, Just loc') -> do
>             setCtx (locs :< loc :< loc')
>             tellUser s
>         (s, Nothing) -> do
>             setCtx (locs :< loc)
>             tellUser "I'm sorry, Dave. I'm afraid I can't do that."
>             tellUser s

>     case runProofState (eval <* startScheduler) loc of
>         (s, Just loc') -> do
>             setCtx (locs :< loc :< loc')
>             tellUser s
>         (s, Nothing) -> do
>             tellUser s
>             tellUser "I'm sorry, Dave. I'm afraid I can't do that."


We have some shortcuts for building common kinds of tactics:
|simpleCT| builds a tactic that works in the proof state,
and there are various specialised versions of it for nullary and
unary tactics.

> simpleCT :: String -> Parsley Token (Bwd CochonArg)
>     -> ([CochonArg] -> ProofState String) -> String -> CochonTactic
> simpleCT name parser eval help = CochonTactic
>     {  ctName = name
>     ,  ctParse = parser
>     ,  ctxTrans = simpleOutput . eval
>     ,  ctHelp = fromString help
>     }

> nullaryCT :: String -> ProofState String -> String -> CochonTactic
> nullaryCT name eval help = simpleCT name (pure B0) (const eval) help

> unaryExCT :: String -> (DExTmRN -> ProofState String) -> String -> CochonTactic
> unaryExCT name eval help = simpleCT
>     name
>     (| (B0 :<) tokenExTm
>      | (B0 :<) tokenAscription |)
>     (eval . argToEx . head)
>     help

> unaryInCT :: String -> (DInTmRN -> ProofState String) -> String -> CochonTactic
> unaryInCT name eval help = simpleCT
>     name
>     (| (B0 :<) tokenInTm |)
>     (eval . argToIn . head)
>     help

> unDP :: DExTm p x -> x
> unDP (DP ref ::$ []) = ref

> unaryNameCT :: String -> (RelName -> ProofState String) -> String -> CochonTactic
> unaryNameCT name eval help = simpleCT
>     name
>     (| (B0 :<) tokenName |)
>     (eval . unDP . argToEx . head)
>     help

> unaryStringCT :: String
>               -> (String -> ProofState String)
>               -> String
>               -> CochonTactic
> unaryStringCT name eval help = simpleCT
>     name
>     (| (B0 :<) tokenString |)
>     (eval . argToStr . head)
>     help

The master list of Cochon tactics.

> cochonTactics :: [CochonTactic]
> cochonTactics = sort (

Construction tactics:


>     nullaryCT "apply" (apply >> return "Applied.")
>       "apply - applies the last entry in the development to a new subgoal."
>   : nullaryCT "done" (done >> return "Done.")
>       "done - solves the goal with the last entry in the development."
>   : unaryInCT "give" (\tm -> elabGiveNext tm >> return "Thank you.")
>       "give <term> - solves the goal with <term>."
>   : simpleCT
>         "lambda"
>          (| (|bwdList (pSep (keyword KwComma) tokenString) (%keyword KwAsc%)|) :< tokenInTm
>           | bwdList (pSep (keyword KwComma) tokenString)
>           |)
>          (\ args -> case args of
>             [] -> return "This lambda needs no introduction!"
>             _ -> case last args of
>               InArg ty  -> Data.Traversable.mapM (elabLamParam . (:<: ty) . argToStr) (init args)
>                                >> return "Made lambda!"
>               _         -> Data.Traversable.mapM (lambdaParam . argToStr) args
>                                >> return "Made lambda!"
>            )
>          ("lambda <labels> - introduces one or more hypotheses.\n"++
>           "lambda <labels> : <type> - introduces new module parameters or hypotheses.")

>   : simpleCT
>         "let"
>         (| (| (B0 :< ) tokenString |) :< tokenScheme |)
>         (\ [StrArg x, SchemeArg s] -> do
>             elabLet (x :<: s)
>             optional' problemSimplify
>             optional' seekGoal
>             return ("Let there be " ++ x ++ "."))
>         "let <label> <scheme> : <type> - set up a programming problem with a scheme."

>   : simpleCT
>         "make"
>         (| (|(B0 :<) tokenString (%keyword KwAsc%)|) :< tokenInTm
>          | (|(B0 :<) tokenString (%keyword KwDefn%) |) <><
>              (| (\ (tm :<: ty) -> InArg tm :> InArg ty :> F0) pAscription |)
>          |)
>         (\ (StrArg s:tyOrTm) -> case tyOrTm of
>             [InArg ty] -> do
>                 elabMake (s :<: ty)
>                 goIn
>                 return "Appended goal!"
>             [InArg tm, InArg ty] -> do
>                 elabMake (s :<: ty)
>                 goIn
>                 elabGive tm
>                 return "Made."
>         )
>        ("make <x> : <type> - creates a new goal of the given type.\n"
>            ++ "make <x> := <term> - adds a definition to the context.")

>   : unaryStringCT "module" (\s -> makeModule s >> goIn >> return "Made module.")
>       "module <x> - creates a module with name <x>."

>   : simpleCT
>         "pi"
>          (| (|(B0 :<) tokenString (%keyword KwAsc%)|) :< tokenInTm |)
>         (\ [StrArg s, InArg ty] -> elabPiParam (s :<: ty) >> return "Made pi!")
>         "pi <x> : <type> - introduces a pi."

>   : simpleCT
>       "program"
>       (|bwdList (pSep (keyword KwComma) tokenString)|)
>       (\ as -> elabProgram (map argToStr as) >> return "Programming.")
>       "program <labels>: set up a programming problem."

>   : nullaryCT "ungawa" (ungawa >> return "Ungawa!")
>       "ungawa - tries to solve the current goal in a stupid way."


Navigation tactics:

>   : nullaryCT "in" (goIn >> return "Going in...")
>       "in - moves to the bottom-most development within the current one."
>   : nullaryCT "out" (goOutBelow >> return "Going out...")
>       "out - moves to the development containing the current one."
>   : nullaryCT "up" (goUp >> return "Going up...")
>       "up - moves to the development above the current one."
>   : nullaryCT "down" (goDown >> return "Going down...")
>       "down - moves to the development below the current one."
>   : nullaryCT "top" (many' goUp >> return "Going to top...")
>       "top - moves to the top-most development at the current level."
>   : nullaryCT "bottom" (many' goDown >> return "Going to bottom...")
>       "bottom - moves to the bottom-most development at the current level."
>   : nullaryCT "previous" (prevGoal >> return "Going to previous goal...")
>       "previous - searches for the previous goal in the proof state."
>   : nullaryCT "root" (many' goOut >> return "Going to root...")
>       "root - moves to the root of the proof state."
>   : nullaryCT "next" ( nextGoal >> return "Going to next goal...")
>       "next - searches for the next goal in the proof state."
>   : nullaryCT "first"  (some' prevGoal >> return "Going to first goal...")
>       "first - searches for the first goal in the proof state."
>   : nullaryCT "last"   (some' nextGoal >> return "Going to last goal...")
>       "last - searches for the last goal in the proof state."

>   : unaryNameCT "jump" (\ x -> do
>       (n := _) <- resolveDiscard x
>       goTo n
>       return ("Jumping to " ++ showName n ++ "...")
>     )
>       "jump <name> - moves to the definition of <name>."


Miscellaneous tactics:

TODO(joel) - I cut out help for now; my thinking being that there should be
ample help already available - a high level overview as well as a filtered list
of available tactics. It wasn't really working because we can only output a
string to the user but ctHelp is a ReactM ()

>      : CochonTactic
>          {  ctName = "help"
>          ,  ctParse = (| (B0 :<) tokenString
>                        | B0
>                        |)
>          ,  ctxTrans = (\args ->
>              case args of
>                  [] -> tellUser $ "Tactics available: " ++ tacticNames cochonTactics
>                  [StrArg s] -> case tacticsMatching s of
>                      [] -> tellUser "There is no tactic by that name."
>                      cts -> displayUser $ Prelude.mapM_ ctHelp cts
>            )
>          ,  ctHelp = fromString $ "help - displays a list of supported tactics.\n"
>                 ++ "help <tactic> - displays help about <tactic>.\n\n"
>                 ++ "What, you expected 'help help' to produce an amusing response?"
>          }

>     : CochonTactic
>         {  ctName = "undo"
>         ,  ctParse = pure B0
>         ,  ctxTrans = (\_ -> do
>                locs :< loc <- getCtx
>                case locs of
>                    B0  -> tellUser "Cannot undo."  >> setCtx (locs :< loc)
>                    _   -> tellUser "Undone."       >> setCtx locs
>          )
>         ,  ctHelp = fromString "undo - goes back to a previous state."
>         }

>     : nullaryCT "validate" (validateHere >> return "Validated.")
>         "validate - re-checks the definition at the current location."

Import more tactics from an aspect:

>     import <- CochonTactics
>     : [] )

> import <- CochonTacticsCode


> doCTacticsAt :: [(Name, [CTData])] -> PageM ()
> doCTacticsAt [] = return ()
> doCTacticsAt ((_, []):ncs) = doCTacticsAt ncs
> doCTacticsAt ((n, cs):ncs) = do
>     locs :< loc <- getCtx
>     let Right loc' = execStateT (goTo n) loc
>     setCtx (locs :< loc :< loc')
>     doCTactics cs
>     doCTacticsAt ncs

> doCTactics :: [CTData] -> PageM ()
> doCTactics = Foldable.mapM_ doCTactic
>     where doCTactic :: CTData -> PageM ()
>           doCTactic = uncurry ctxTrans

> pFileName :: Parsley Token String
> pFileName = ident


> tokenizeCommands :: Parsley Char [String]
> tokenizeCommands = (|id ~ [] (% pEndOfStream %)
>                     |id (% oneLineComment %)
>                         (% consumeUntil' endOfLine %)
>                         tokenizeCommands
>                     |id (% openBlockComment %)
>                         (% (eatNestedComments 0) %)
>                         tokenizeCommands
>                     |id (spaces *> endOfLine *> tokenizeCommands)
>                     |consumeUntil' endOfCommand :
>                      tokenizeCommands
>                     |)
>     where endOfCommand = tokenEq ';' *> spaces *> endOfLine
>                      <|> pEndOfStream *> pure ()
>           endOfLine = tokenEq (head "\n") <|> pEndOfStream
>           oneLineComment = tokenEq '-' *> tokenEq '-'
>           openBlockComment = tokenEq '{' *> tokenEq '-'
>           closeBlockComment = tokenEq '-' *> tokenEq '}'
>           spaces = many $ tokenEq ' '
>           eatNestedComments (-1) = (|id ~ ()|)
>           eatNestedComments i = (|id  (% openBlockComment %)
>                                       (eatNestedComments (i+1))
>                                  |id (% closeBlockComment %)
>                                      (eatNestedComments (i-1))
>                                  |id (% nextToken %)
>                                      (eatNestedComments i) |)

> pCochonTactics :: Parsley Token [CTData]
> pCochonTactics = pSepTerminate (keyword KwSemi) pCochonTactic


> pCochonTactic :: Parsley Token CTData
> pCochonTactic  = do
>     x <- (|id ident
>           |key anyKeyword
>           |)
>     case tacticsMatching x of
>         [ct] -> do
>             args <- ctParse ct
>             return (ct, trail args)
>         [] -> fail "unknown tactic name."
>         cts -> fail $
>             "ambiguous tactic name (could be " ++ tacticNames cts ++ ").")
