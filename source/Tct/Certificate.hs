{- | 
Module      :  Tct.Certificate
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
License     :  LGPL (see COPYING)

Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

This module defines the 'Certificate' and 'Complexity' datatype, 
together with accessors.
-}

module Tct.Certificate
    ( 
      -- * Complexity 
      
      Complexity (..)
      -- | The datatype 'Complexity' is TcTs representation
      -- of a bounding function, in big-O notation
      
      -- ** Constructors
    , constant
      -- | Constructor for constant bounding function.
    , poly
      -- | Constructor for polynomial bounding function, with optional degree.
    , expo
      -- | Constructor for elementary (k-exponential) bounding function.
    , supexp
      -- | Constructor for super exponential bounding function.
    , primrec
      -- | Constructor for primitive recursive bounding function.      
    , unknown      
      
      -- ** Combinations
    , add
      -- | Addition of bounds modulo big-O notation, i.e., @f ``add`` g@ so 
      -- constructs an element of 'Complexity' that majorises @O(f(n)) + O(g(n))@.
    , mult
      -- | Multiplication of bounds modulo big-O notation, i.e., @f ``mult`` g@ so 
      -- constructs an element of 'Complexity' that majorises @O(f(n)) + O(g(n))@.
    , compose
      -- | Composition of bounds modulo big-O notation, i.e., @f ``compose`` g@ so 
      -- constructs an element of 'Complexity' that majorises @O(f(g(n)))@.
    , iter
      -- | Iteration of bounds modulo big-O notation, i.e., @f ``iter`` g@ so 
      -- constructs an element of 'Complexity' that majorises @O(f(..f(n)..))@ 
      -- with @O(m)@ occurences of @f@.
      
      -- * Complexity Certificate
    , Certificate 
      -- | A certificate consists of a lower and an upper bound. 
    , lowerBound
      -- | Extract the lower bound from a 'Certificate'.
    , upperBound
      -- | Extract the upper bound from a 'Certificate'.
    , certified
      -- | The call @certificate (l,u)@ constructs a 'Certificate' 
      -- with lower bound @l@ and upper bound @u@.
    , uncertified
      -- | Constructs a 'Certificate' where both lower and upper bounds are unknown.
    )
where 
import Termlib.Utils (PrettyPrintable(..), Parsable(..))
import Text.Parsec.Prim
import Text.Parsec.Combinator
import Text.ParserCombinators.Parsec.Char
import Text.PrettyPrint.HughesPJ hiding (char)

data Complexity = Poly (Maybe Int) -- ^ Polynomial. If argument is @Just k@, then 
                                   -- @k@ gives the degree of the polynomial
                | Exp (Maybe Int) -- ^ Exponential. If argument is @Nothing@, then 
                                  -- represented bounding function is elementary. If argument 
                                  -- is @Just k@, then bounding function is k-exponential. 
                                  -- Hence @Exp (Just 1)@ represents an exponential bounding 
                                  -- function. 
                | Supexp -- ^ Super exponential.
                | Primrec -- ^ Primitive recursive.
                | Multrec -- ^ Multiple recursive.
                | Rec -- ^ Recursive.
                | Unknown -- ^ Unknown.
                deriving (Eq, Show)

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

compose :: Complexity -> Complexity -> Complexity
(Poly (Just n)) `compose` a               | n == 0 = Poly (Just 0)
                                          | n == 1 = a
a               `compose` (Poly (Just m)) | m == 0 = Poly (Just 0)
                                          | m == 1 = a
(Poly (Just n)) `compose` (Poly (Just m))          = Poly $ Just $ n * m
(Poly Nothing)  `compose` (Poly _)                 = Poly Nothing
(Poly _)        `compose` (Poly Nothing)           = Poly Nothing
(Exp (Just n))  `compose` (Poly _)                 = Exp $ Just $ n + 1
(Poly _)        `compose` (Exp (Just m))           = Exp $ Just m
(Exp (Just n))  `compose` (Exp (Just m))           = Exp $ Just $ n + m
(Exp Nothing)   `compose` (Exp _)                  = Exp Nothing
(Exp _)         `compose` (Exp Nothing)            = Exp Nothing
a               `compose` b                        = maximum [Primrec, a, b]

iter :: Complexity -> Complexity -> Complexity
(Poly (Just n)) `iter` _        | n == 0 = Poly $ Just 0
(Poly (Just n)) `iter` (Poly m) | n == 1 = case m of
                                             Just 0 -> Poly $ Just 1
                                             Just 1 -> Exp $ Just 1
                                             _      -> Exp $ Just 2
(Poly n)        `iter` (Exp _)  | n == Just 0 = Exp Nothing
                                | n == Just 1 = Supexp
                                | otherwise   = Primrec
(Poly _)        `iter` b                      = max Primrec b
(Exp _)         `iter` (Poly m) | m == Just 0 = Exp Nothing
                                | m == Just 1 = Supexp
                                | otherwise   = Primrec
a               `iter` b                      = maximum [Primrec, a, b]

newtype Certificate = Cert (Complexity, Complexity) deriving (Show)

certified :: (Complexity, Complexity) -> Certificate
certified (l,u) = Cert (l, u)

lowerBound :: Certificate -> Complexity
lowerBound (Cert (l,_)) = l

upperBound :: Certificate -> Complexity
upperBound (Cert (_,u)) = u

poly :: Maybe Int -> Complexity
poly = Poly

constant :: Complexity
constant = Poly (Just 0)

expo :: Maybe Int -> Complexity
expo = Exp

supexp :: Complexity
supexp = Supexp

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
          pPrec       = string "PRIMREC" >> return Primrec
          pMrec       = string "MULTREC" >> return Multrec
          pRec        = string "REC" >> return Rec
          pUnknown    = string "?" >> return Unknown
          pInt        = many1 digit >>= return . read


instance PrettyPrintable Complexity where
    pprint (Poly Nothing)  = text "POLY"
    pprint (Poly (Just 0)) = text "O(1)"
    pprint (Poly (Just n)) = text "O(n^" <> text (show n) <> text ")"
    pprint (Exp Nothing)   = text "ELEMENTARY"
    pprint (Exp (Just n))  = text "ELEMENTARY" <> (parens $ text $ show n)
    pprint Supexp          = text "SUPEREXPONENTIAL"
    pprint Primrec         = text "PRIMREC"
    pprint Multrec         = text "MULTREC"
    pprint Rec             = text "REC"
    pprint Unknown         = text "?"

instance PrettyPrintable Certificate where 
  pprint c = text "YES" <> (parens $ (pprint $ lowerBound c) <>  text "," <> (pprint $ upperBound c))

uncertified :: Certificate
uncertified = Cert (Unknown, Unknown)