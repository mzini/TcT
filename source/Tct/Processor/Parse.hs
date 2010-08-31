{-
This file is part of the Tyrolean Complexity Tool (TCT).

The Tyrolean Complexity Tool is free software: you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

The Tyrolean Complexity Tool is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License
along with the Tyrolean Complexity Tool.  If not, see <http://www.gnu.org/licenses/>.
-}

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
