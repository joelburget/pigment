Loading Developments
====================

> {-# LANGUAGE TypeOperators #-}

> module Cochon.DevLoad (devLoad, devLoad', doCTactics, pTactic) where

> import Control.Applicative
> import Control.Error
> import Control.Exception (catch)
> import Control.Monad.State
> import Control.Monad.Writer
> import Data.Foldable as Foldable
> import Data.Functor
> import Data.List
> import Data.Traversable
> import qualified Data.Text as T
> import Data.Text (Text)
> import System.Exit
> import System.FilePath
> import System.IO

> import Kit.BwdFwd
> import Kit.MissingLibrary
> import Kit.Parsley
> import Kit.Trace
> import Cochon.CommandLexer
> import Cochon.Controller
> import Cochon.Tactics
> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.Lexer
> import DisplayLang.TmParse
> import DisplayLang.PrettyPrint
> import Elaboration.Elaborator
> import Elaboration.Error
> import Evidences.Tm
> import NameSupply.NameSupply
> import NameSupply.NameSupplier
> import ProofState.Structure.Developments
> import ProofState.Edition.Entries
> import ProofState.Edition.ProofContext
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation
> import ProofState.Interface.Module
> import ProofState.Interface.NameResolution
> import ProofState.Interface.Search

Parsing a Development
---------------------

To parse a development, we represent it as a list of `DevLine`s, each of
which corresponds to a `Parameter` or `Definition` entry and stores
enough information to reconstruct it. Note that at this stage, we simply
tag each definition with a list of commands to execute later.

> data DevLine
>   =  DLParam ParamKind String DInTmRN
>   |  DLDef String [DevLine] (Maybe DInTmRN :<: DInTmRN) [CTData]
>   |  DLModule String [DevLine] [CTData]

A module may have a list of definitions in square brackets, followed by
an optional semicolon-separated list of commands.

> parseDevelopment :: Parsley Token [DevLine]
> parseDevelopment = bracket Square (many (pDef <|> pModule))
>                <|> pure []

Parsing definitions

A definition is an identifier, followed by a list of children, a
definition (which may be `?`), and optionally a list of commands:

> pDef :: Parsley Token DevLine
> pDef =  DLDef
>     <$> ident                  -- identifier
>     <*> pLines                 -- childrens (optional)
>     <*> pDefn                  -- definition
>     <*> pCTSuffix              -- commands (optional)
>     <* keyword KwSemi

Parsing children:

Children, if any, are enclosed inside square brackets. They can be of
several types: definitions, that we have already defined, or parameters.
Parameters are defined below. The absence of sub-development is signaled
by the `:=` symbol.

> pLines  :: Parsley Token [DevLine]
> pLines  =  bracket Square (many (pDef <|> pParam <|> pModule))
>         <|> (keyword KwDefn *> pure [])

Parsing definitions:

A definition is either a question mark or a term, ascripted by a type.
The question mark corresponds to an open goal. On the other hand, giving
a term corresponds to explicitly solving the goal.

> pDefn :: Parsley Token (Maybe DInTmRN :<: DInTmRN)
> pDefn = (identEq "?" >> keyword KwAsc >> (Nothing :<:) <$> pDInTm)
>     <|> pAsc
>   where pAsc = do
>          tm :<: ty <- pAscription
>          return $ Just tm :<: ty

Parsing commands:

Commands can be typed directly in the developments by enclosing them
inside `[| ... |]` brackets. They are parsed in one go by
`pTactics`, so this is quite fragile. This is better used when we
know things work.

> pCTSuffix  :: Parsley Token [CTData]
> pCTSuffix = pure []

pCTSuffix  = bracket (SquareB "") pTactics
           <|> pure []

Parsing Modules

A module is similar, but has no definition.

> pModule :: Parsley Token DevLine
> pModule =  DLModule
>     <$> ident                  -- identifier
>     <*> pLines                 -- children (optional)
>     <*> pCTSuffix              -- commands (optional)
>     <* keyword KwSemi

Parsing Parameters

A parameter is a $\lambda$-abstraction (represented by `x : T ->`) or
a $\Pi$-abstraction (represented by `(x : S) ->`).

> pParam :: Parsley Token DevLine
> pParam =  (keyword KwLambda        -- @\@
>       $> DLParam ParamLam
>      <*> ident                     -- @x@
>      <*  keyword KwAsc             -- @:@
>      <*> sizedDInTm (pred ArrSize) -- @T@
>      <*  keyword KwArr)            -- @->@
>      <|>
>      bracket Round                 -- @(@
>          (DLParam ParamPi
>               <$> ident            -- @x@
>               <*  keyword KwAsc    -- @:@
>               <*> pDInTm
>          )                         -- @S)@
>      <* keyword KwArr              -- @->@

Construction
------------

Once we have parsed a development as a list of `DevLine`, we interpret
it in the `ProofState` monad. This is the role of `makeDev`. It updates
the proof state to represent the given list of `DevLine`s, accumulating
pairs of names and command lists along the way.

> type NamedCommand = (Name, [CTData])

> makeDev :: [DevLine] -> [NamedCommand] -> ProofState [NamedCommand]
> makeDev []      ncs = return ncs
> makeDev (l:ls)  ncs = makeEntry l ncs >>= makeDev ls

Each line of development is processed by `makeEntry`. This is where the
magic happen and the `ProofState` is updated.

> makeEntry :: DevLine -> [NamedCommand] -> ProofState [NamedCommand]

Making a definition:

To make a definition, we operate in 4 steps. First of all, we jump in a
module in which we make our kids. Once this is done, we resolve our
display syntax goal into a term: we are therefore able to turn the
module in a definition. The third step consists in solving the problem
if we were provided a solution, or give up if not. Finally, we
accumulate the commands which might have been issued.

> makeEntry (DLDef x kids (mtipTm :<: tipTys) commands) ncs = do
>     -- Open a module named by her name
>     n <- makeModule DevelopOther x
>     goIn
>     -- Recursively build the kids
>     ncs' <- makeDev kids ncs
>     -- Translate `tipTys` into a real `INTM`
>     tipTy :=>: tipTyv <- elaborate' (SET :>: tipTys)
>     -- Turn the module into a definition of `tipTy`
>     moduleToGoal tipTy
>     -- Were we provided a solution?
>     case mtipTm of
>         -- No? Leave.
>         Nothing -> goOut
>         Just tms -> do -- Yes!
>             -- Give the solution `tms`
>             elabGive tms
>             return ()
>     -- Is there any tactics to be executed?
>     return $ case commands of
>         -- No? Return the kids' commands.
>         []  -> ncs'
>         -- Yes! Accumulate our commands with the ones from the kids.
>         _   -> (n, commands) : ncs'

Making a Module:

Making a module involves much less effort than to make a definition.
This is indeed a stripped-down version of the above code for
definitions.

> makeEntry (DLModule x kids commands) ncs = do
>     -- Make the module
>     n <- makeModule DevelopModule x
>     goIn
>     -- Recursively build the kids
>     ncs' <- makeDev kids ncs
>     -- Leave
>     goOut
>     -- Is there any tactics to be executed?
>     return $ case commands of
>         -- No? Return the kids' commands.
>         []  -> ncs'
>         -- Yes! Accumulate our commands with the ones from the kids.

>         _   -> (n, commands) : ncs'

Making a Parameter:

To make a parameter, be it Lambda or Pi, is straightforward. First, we
need to translate the type in display syntax to an `INTM`. Then, we make
a fresh reference of that type. Finally, we store that reference in the
development.

> makeEntry (DLParam k x tys) ncs = do
>     -- Translate the display `tys` into an `INTM`
>     ty :=>: tyv <- elaborate' (SET :>: tys)
>     -- Make a fresh reference of that type
>     freshRef (x :<: tyv) (\ref ->
>         -- Register `ref` as a Lambda
>         putEntryAbove (EPARAM ref (mkLastName ref) k ty AnchNo emptyMetadata))
>     -- Pass the accumulated commands
>     return ncs

\subsection{Loading the files}

Once we have parsed a list of |DevLine|s, we need to construct a |Dev|
from them.  The idea is to use commands defined in
Section~\ref{sec:ProofState.Edition.ProofState} to build up the proof
state.

> devLoad :: [CochonTactic] -> String -> IO (Bwd ProofContext)
> devLoad tacs file =
>   -- Load the development file
>   let devFile = dropExtension file ++ ".dev"
>   in withFile devFile ReadMode $ \devFileH ->
>       let ctDataCmd = withFile file ReadMode (readCommands tacs)
>       in devLoad' tacs devFileH ctDataCmd

> devLoad' :: [CochonTactic] -> Handle -> IO [CTData] -> IO (Bwd ProofContext)
> devLoad' tacs fileH commandLoad = do
>   -- Load the development file
>   dev <- loadDevelopment fileH
>   -- Load the development in an empty proof state
>   case runStateT (makeDev dev [] `catchStack` catchUnprettyErrors) emptyContext of
>     Left errs -> do
>       putStrLn "Failed to load development:"
>       putStrLn $ renderHouseStyle $ prettyStackError errs
>       exitFailure
>     Right (ncs, loc) -> do
>       -- Load the commands
>       commands <- commandLoad
>       -- Run them
>       doCTacticsAt (([], commands) : ncs) (B0 :< loc)


The following companion function takes care of the dirty details:
\begin{itemize}
\item Loading the content of the file;
\item Tokenizing the file
\item Parsing the development
\end{itemize}

> loadDevelopment :: Handle -> IO [DevLine]
> loadDevelopment file = do
>     f <- hGetContents file
>     -- Tokenize the development file
>     case parse tokenize f of
>       Left err -> do
>         putStrLn $ "loadDevelopment: failed to tokenize:\n" ++
>                    show err
>         exitFailure
>       Right toks ->
>           -- Parse the development
>           case parse parseDevelopment toks of
>             Left err -> do
>               putStrLn $ "loadDevelopment: failed to parse:\n" ++
>                            show err
>               exitFailure
>             Right dev -> do
>               -- Return the result
>               return dev

> readCommands :: [CochonTactic] -> Handle -> IO [CTData]
> readCommands tacs file = do
>   f <- hGetContents file
>   case parse tokenizeCommands f of
>     Left err -> do
>       putStrLn $ "readCommands: failed to tokenize:\n" ++
>                  show err
>       exitFailure
>     Right lines -> do
>          t <- Data.Traversable.sequence $ map (readCommand tacs) lines
>          return $ Data.List.concat t

> readCommand :: [CochonTactic] -> String -> IO [CTData]
> readCommand tacs command =
>     case parse tokenize command of
>       Left err -> do
>         putStrLn $ "readCommand: failed to tokenize:\n" ++
>                    show err
>         putStrLn $ "Input was: " ++ command
>         exitFailure
>       Right toks -> do
>         print toks
>         -- case parse (pTactics tacs) toks of
>         case parse (pTactic tacs) toks of
>           Left err -> do
>             putStrLn $ "readCommand: failed to parse:\n" ++
>                        show err
>             putStrLn $ "Input was: " ++ command
>             exitFailure
>           Right command -> return [command]


> tokenizeCommands :: Parsley Char [String]
> tokenizeCommands = [] <$ pEndOfStream
>                <|> (oneLineComment *> consumeUntil' endOfLine *> tokenizeCommands)
>                <|> (openBlockComment *> eatNestedComments 0 *> tokenizeCommands)
>                <|> (spaces *> endOfLine *> tokenizeCommands)
>                <|> ((:) <$> consumeUntil' endOfCommand <*> tokenizeCommands)
>     where endOfCommand = tokenEq ';' *> spaces *> endOfLine
>                      <|> pEndOfStream *> pure ()
>           endOfLine = tokenEq (head "\n") <|> pEndOfStream
>           oneLineComment = tokenEq '-' *> tokenEq '-'
>           openBlockComment = tokenEq '{' *> tokenEq '-'
>           closeBlockComment = tokenEq '-' *> tokenEq '}'
>           spaces = many $ tokenEq ' '
>           eatNestedComments (-1) = pure ()
>           eatNestedComments i = openBlockComment *> eatNestedComments (i+1)
>                             <|> closeBlockComment *> eatNestedComments (i-1)
>                             <|> nextToken *> eatNestedComments i

> tacticNamed :: [CochonTactic] -> Text -> Maybe CochonTactic
> tacticNamed tacs x = Foldable.find ((== x) . ctName) tacs

> pTactic :: [CochonTactic] -> Parsley Token CTData
> pTactic tacs = do
>     x <- ident <|> (key <$> anyKeyword)
>     case tacticNamed tacs (T.pack x) of
>         Just ct -> do
>             elabTrace $ "found tactic named " ++ (T.unpack $ ctName ct)
> -- parseTactic :: TacticDescription -> Parsley Token TacticResult
>             args <- parseTactic (ctDesc ct)
>             elabTrace $ "found args"
>
>             -- trailing semicolons are cool, or not
>             -- XXX(joel)
>             optional (tokenEq (Keyword KwSemi))
>
>             -- this parser is not gonna be happy if there are args left
>             -- over
>             return (ct, args)
>         Nothing -> fail "unknown tactic name."


> pTactics :: [CochonTactic] -> Parsley Token [CTData]
> pTactics tacs = pSepTerminate (keyword KwSemi) (pTactic tacs)


> runCmd :: Cmd a -> Bwd ProofContext -> (String, Bwd ProofContext)
> runCmd cmd ctx =
>     let ((_, msg), ctx') = runState (runWriterT cmd) ctx
>     in (msg, ctx')


> doCTactic :: CTData -> Bwd ProofContext -> IO (Bwd ProofContext)
> doCTactic (ct, args) ctx =
>     let (msg, ctx') = runCmd (ctxTrans ct args) ctx
>     in do print msg
>           return ctx'

> doCTactics :: [CTData] -> Bwd ProofContext -> IO (Bwd ProofContext)
> doCTactics [] locs = return locs
> doCTactics (cd:cds) locs = do
>     locs' <- doCTactic cd locs
>     doCTactics cds locs'

> doCTacticsAt :: [(Name, [CTData])] -> Bwd ProofContext -> IO (Bwd ProofContext)
> doCTacticsAt [] locs = return locs
> doCTacticsAt ((_, []):ncs) locs = doCTacticsAt ncs locs
> doCTacticsAt ((n, cs):ncs) (locs :< loc) = do
>     let Right loc' = execStateT (goTo n) loc
>     locs' <- doCTactics cs (locs :< loc :< loc')
>     doCTacticsAt ncs locs'

> printChanges :: ProofContext -> ProofContext -> IO ()
> printChanges from to = do
>     let Right as = evalStateT getInScope from
>         Right bs = evalStateT getInScope to
>     let (lost, gained)  = diff (as <>> F0) (bs <>> F0)
>     if lost /= F0
>         then putStrLn ("Left scope: " ++ showEntriesAbs (fmap reverseEntry (NF (fmap Right lost))) )
>         else return ()
>     if gained /= F0
>        then putStrLn ("Entered scope: " ++ showEntriesAbs (fmap reverseEntry (NF (fmap Right gained))))
>        else return ()

> diff :: (Eq a, Show a) => Fwd a -> Fwd a -> (Fwd a, Fwd a)
> diff (x :> xs) (y :> ys)
>     | x == y     = diff xs ys
>     | otherwise  = (x :> xs, y :> ys)
> diff xs ys = (xs, ys)
