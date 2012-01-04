--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Processor.Parse
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module defines utilities for parsing processors.
--------------------------------------------------------------------------------   

module Tct.Processor.Parse
 ( parseTimeout
 , natural
 , double
 , identifier
 , whiteSpace
 , bool
 , eltOf
 , stringLit
 , parens
 , brackets
 , fromString)
where
import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language (haskellDef)
import Control.Monad (liftM)

parseTimeout :: CharParser st (Maybe Int)
parseTimeout = optionMaybe $ (brackets spec <?> "[<timeout>]")
  where spec  = do n <-  number
                   return $ n * (10^(6 :: Int))
        number = try (double >>= return . round) <|> natural

lexer :: P.TokenParser st
lexer = P.makeTokenParser haskellDef
      
identifier :: CharParser st String
identifier = P.identifier lexer

natural :: CharParser st Int
natural = fromIntegral `liftM` P.natural lexer

double :: CharParser st Double
double =  P.float lexer

bool :: CharParser st Bool
bool = try (string "On" >> return True) <|> (string "Off" >> return False)

eltOf :: [String] -> CharParser st String
eltOf as = choice [try $ string a | a <- as]

stringLit :: CharParser st String
stringLit = P.stringLiteral lexer

whiteSpace :: CharParser st () 
whiteSpace = P.whiteSpace lexer

parens :: CharParser st a -> CharParser st a
parens = P.parens lexer

brackets :: CharParser st a -> CharParser st a
brackets = P.brackets lexer

fromString :: CharParser st a -> st -> SourceName -> String -> Either ParseError a
fromString pp = runParser $ do {p <- pp; eof; return p}
