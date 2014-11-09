


cochon' :: Bwd ProofContext -> IO ()
cochon' (InteractionState (locs :< loc) iput oput) = do
    -- Safety belt: this *must* type-check!
    validateDevelopment (locs :< loc)
    -- Show goal and prompt
    putStr $ fst $ runProofState showPrompt loc
    -- hFlush stdout
    l <- requestInput
    case parse tokenize l of
        Left pf -> do
            putStrLn ("Tokenize failure: " ++ describePFailure pf id)
            cochon' (locs :< loc)
        Right ts ->
          case parse pCochonTactics ts of
              Left pf -> do
                  putStrLn ("Parse failure: " ++ describePFailure pf (intercalate " " . map crushToken))
                  cochon' (locs :< loc)
              Right cds -> do
                  locs' <- doCTactics cds (locs :< loc)
                  cochon' locs'

readCommands :: Handle -> IO [CTData]
readCommands file = do
  f <- hGetContents file
  case parse tokenizeCommands f of
    Left err -> do
      putStrLn $ "readCommands: failed to tokenize:\n" ++
                 show err
      exitFailure
    Right lines -> do
         t <- Data.Traversable.sequence $ map readCommand lines
         return $ Data.List.concat t

readCommand :: String -> IO [CTData]
readCommand command =
    case parse tokenize command of
      Left err -> do
        putStrLn $ "readCommand: failed to tokenize:\n" ++
                   show err
        putStrLn $ "Input was: " ++ command
        exitFailure
      Right toks -> do
        case parse pCochonTactics toks of
          Left err -> do
            putStrLn $ "readCommand: failed to parse:\n" ++
                       show err
            putStrLn $ "Input was: " ++ command
            exitFailure
          Right command -> do
            return command

printChanges :: ProofContext -> ProofContext -> IO ()
printChanges from to = do
    let Right as = evalStateT getInScope from
        Right bs = evalStateT getInScope to
    let (lost, gained)  = diff (as <>> F0) (bs <>> F0)
    if lost /= F0
        then putStrLn ("Left scope: " ++ showEntriesAbs (fmap reverseEntry (NF (fmap Right lost))) )
        else return ()
    if gained /= F0
       then putStrLn ("Entered scope: " ++ showEntriesAbs (fmap reverseEntry (NF (fmap Right gained))))
       else return ()

diff :: (Eq a, Show a) => Fwd a -> Fwd a -> (Fwd a, Fwd a)
diff (x :> xs) (y :> ys)
    | x == y     = diff xs ys
    | otherwise  = (x :> xs, y :> ys)
diff xs ys = (xs, ys)
