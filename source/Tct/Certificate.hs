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

module Tct.Certificate
    ( Complexity (..)
    , Certificate 
    , lowerBound
    , upperBound
    , certified
    , uncertified
    , add 
    , mult
    , poly
    , expo
    , primrec
    , unknown
    )
where 
import Termlib.Utils (PrettyPrintable(..), Parsable(..))
import Text.Parsec.Prim
import Text.Parsec.Combinator
import Text.ParserCombinators.Parsec.Char
import Text.PrettyPrint.HughesPJ hiding (char)

data Complexity = Poly (Maybe Int)
                | Exp (Maybe Int)
                | Supexp
                | Primrec
                | Multrec
                | Rec 
                | Unknown deriving (Eq, Show)

rank :: Complexity -> (Int, Int)
rank (Poly (Just r)) = (42,r)
rank (Poly _)        = (43,0)
rank (Exp (Just r))  = (44,r)
rank (Exp _)         = (45,0)
rank Supexp          = (46,0)
rank Primrec         = (47,0)
rank Multrec         = (48,0)
rank Rec             = (49,0)
rank Unknown         = (142,0)

instance Ord Complexity where
  c1 <= c2 = a1 < a2 || (a1 == a2 && b1 <= b2)
    where (a1,b1) = rank c1
          (a2,b2) = rank c2

add :: Complexity -> Complexity -> Complexity
add = max

mult :: Complexity -> Complexity -> Complexity
(Poly (Just n)) `mult` (Poly (Just m)) = Poly $ Just $ n + m
(Poly Nothing)  `mult` (Poly _)        = Poly Nothing
(Poly _)        `mult` (Poly Nothing)  = Poly Nothing
(Exp (Just n))  `mult` (Exp (Just m))  = Exp $ Just $ max n m    
(Exp Nothing)   `mult` (Exp _)         = Exp Nothing
a               `mult` b               = max a b

newtype Certificate = Cert (Complexity, Complexity) deriving (Show)

certified :: (Complexity, Complexity) -> Certificate
certified (l,u) = Cert (l, u)

lowerBound :: Certificate -> Complexity
lowerBound (Cert (l,_)) = l

upperBound :: Certificate -> Complexity
upperBound (Cert (_,u)) = u

poly :: Maybe Int -> Complexity
poly = Poly

expo :: Maybe Int -> Complexity
expo = Exp

primrec :: Complexity
primrec = Primrec

unknown :: Complexity
unknown = Unknown

instance Eq Certificate where
  (Cert (l1,c1)) ==  (Cert (l2,c2)) = l1 == l2 && c1 == c2

--MA:TODO: should we consider lower bounds?
instance Ord Certificate where
  (Cert (_,c1)) <=  (Cert (_,c2)) = c1 <= c2

instance Parsable Certificate where
  parse = do _ <- string "YES"
             _ <- char '('
             l <- parseBound
             _ <- char ','
             u <- parseBound
             _ <- char ')'
             return $ Cert (l, u)
    where parseBound  = try pPoly <|> pSpecPoly <|> pElem <|> pSupexp <|> pPrec <|> pMrec <|> pRec <|> pUnknown
          pPoly       = string "POLY" >> return (Poly Nothing)
          pSpecPoly   = do _   <- string "O("
                           deg <- pPolyDegree
                           _   <- char ')'
                           return $ Poly $ Just deg
          pPolyDegree = (char '1' >> return 0) <|> (string "n^" >> pInt)
          pElem       = do _ <- string "ELEMENTARY"
                           pSpecElem <|> return (Exp Nothing)
          pSpecElem   = do _ <- char '('
                           n <- pInt
                           _ <- char ')'
                           return $ Exp $ Just n
          pSupexp     = string "SUPEREXPONENTIAL" >> return Supexp
          pPrec       = string "PRIMITIVE RECURSIVE" >> return Primrec
          pMrec       = string "MULTIPLE RECURSIVE" >> return Multrec
          pRec        = string "RECURSIVE" >> return Rec
          pUnknown    = string "?" >> return Unknown
          pInt        = many1 digit >>= return . read


instance PrettyPrintable Complexity where
    pprint (Poly Nothing)  = text "POLY"
    pprint (Poly (Just 0)) = text "O(1)"
    pprint (Poly (Just n)) = text "O(n^" <> text (show n) <> text ")"
    pprint (Exp Nothing)   = text "ELEMENTARY"
    pprint (Exp (Just n))  = text "ELEMENTARY" <> (parens $ text $ show n)
    pprint Supexp          = text "SUPEREXPONENTIAL"
    pprint Primrec         = text "PRIMITIVE RECURSIVE"
    pprint Multrec         = text "MULTIPLE RECURSIVE"
    pprint Rec             = text "RECURSIVE"
    pprint Unknown         = text "?"

instance PrettyPrintable Certificate where 
  pprint c = text "YES" <> (parens $ (pprint $ lowerBound c) <>  text "," <> (pprint $ upperBound c))

uncertified :: Certificate
uncertified = Cert (Unknown, Unknown)