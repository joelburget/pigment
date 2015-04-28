module DisplayLang.QQ (qqDInTmRN) where

import Control.Monad
import Language.Haskell.TH
import Language.Haskell.TH.Quote

import Kit.Parsley
import DisplayLang.DisplayTm
import DisplayLang.Lexer
import DisplayLang.Name
import DisplayLang.TmParse

qqDInTmRN :: QuasiQuoter
qqDInTmRN = QuasiQuoter
    { quoteExp = parseDInTm -- quoteDInTmExp
    -- , quotePat = quoteDInTmPat
    }

-- quoteDInTmExp :: String -> Q Exp
-- quoteDInTmExp s = do
--     expr <- parseDInTm s
--     dataToExpQ (const Nothing) expr

parseDInTm :: Monad m => String -> m DInTmRN
parseDInTm s = case parse tokenize s of
    Left err -> fail $ show err
    Right tokens -> case parse pDInTm tokens of
        Left err -> fail $ show err
        Right tm -> return tm
-- parseDInTm s = case (parse tokenize >=> parse pDInTm) s of
--     Left err -> fail $ show err
--     Right e  -> return e
