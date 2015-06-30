
-- A place to put all the monadic pre-collection before it's rendered in the
-- view
--
-- TODO change name
--
-- TODOs
-- * remove reactHere
-- * remove all uses of ProofState
-- * define data types to encompass them


reactHere :: (TY :>: INTM) -> ProofState TermReact
reactHere tt = do
    dtm :=>: _ <- distillHere tt
    return (reactify dtm :: TermReact)


-- This instance is kind of strange, but should work.
instance ToJSRef Bracket where
    toJSRef = (castRef <$>) . toJSRef' where
        toJSRef' Round = toJSRef "("
        toJSRef' Square = toJSRef "["
        toJSRef' Curly = toJSRef "{"
        toJSRef' (RoundB str) = toJSRef $ "(" ++ str
        toJSRef' (SquareB str) = toJSRef $ "[" ++ str
        toJSRef' (CurlyB str) = toJSRef $ "{" ++ str


instance ToJSRef Keyword where
instance ToJSRef TacticDescription where


instance Reactive EntityAnchor where
    reactify x = span_ [ class_ "anchor" ] $ fromString $ show x

instance (ToJSRef a, ToJSRef b) => ToJSRef (Either a b) where
    toJSRef (Left a) = do
        obj <- newObj
        a' <- toJSRef a
        let propName :: JSString
            propName = "left"
        setProp propName a' obj
        return obj

    toJSRef (Right b) = do
        obj <- newObj
        b' <- toJSRef b
        let propName :: JSString
            propName = "right"
        setProp propName b' obj
        return obj
