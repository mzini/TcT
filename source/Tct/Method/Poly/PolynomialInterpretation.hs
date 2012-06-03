{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_HADDOCK prune #-}

{- | 
Module      :  Tct.Method.Poly.PolynomialInterpretation
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Andreas Schnabl <andreas.schnabl@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

This module defines polynomial interpretations.
-}


module Tct.Method.Poly.PolynomialInterpretation 
       (
         -- * Shapes 
       PolyShape (..)
       , SimplePolyShape (..)
         -- ** Constructors for Custom Shapes
       , SimpleMonomial
       , (^^^)
       , mono
       , constant
       , boolCoefficient
         
         -- hidden
       , PIKind (..)
       , PIVar (..)
       , PolyInter (..)
       , abstractInterpretation
       , toXml
       , degrees
       ) 
       where

import Data.Typeable
import Tct.Utils.PPrint (Align(..), columns)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ

import qualified Qlogic.NatSat as N
import Qlogic.PropositionalFormula
import Qlogic.Semiring

import Termlib.Utils hiding (columns)
import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Variable as V

import qualified Tct.Utils.Xml as Xml
import Tct.Processor.Args.Instances (AssocArgument (..))
import Tct.Encoding.HomomorphicInterpretation
import Tct.Encoding.Polynomial
import qualified Tct.Encoding.UsablePositions as UArgs

data PolyInter a = 
  PI { signature :: F.Signature
     , interpretations :: Map.Map F.Symbol (VPolynomial a) }
  deriving Show

data PIVar = 
  PIVar { restrict :: Bool
        , varfun :: F.Symbol
        , argpos :: [Power V.Variable] }
  deriving (Eq, Ord, Show, Typeable)

type VPolynomial a = Polynomial V.Variable a
-- type VMonomial a = Monomial V.Variable a

-- | A 'SimpleMonomial' denotes a monomial with variables in 'Variable', 
-- and can be build using '^^^', 'constant' and 'mono'.
data SimpleMonomial = SimpleMonomial {smPowers :: [Power V.Variable]}
                    | CoefficientMonomial {smPowers :: [Power V.Variable]}

-- | This datatype reflects standard shapes for polynomial 
-- interpretations, as found in the literature.
data SimplePolyShape = StronglyLinear
                     | Linear
                     | Simple
                     | SimpleMixed
                     | Quadratic
               deriving (Typeable)

-- | The shape of polynomial interpretations.

data PolyShape = SimpleShape SimplePolyShape                      
               | CustomShape ([V.Variable] -> [SimpleMonomial])
               deriving (Typeable)
data PIKind = UnrestrictedPoly PolyShape
            | ConstructorBased (Set.Set F.Symbol) PolyShape
            deriving Show 

instance PropAtom PIVar

instance Functor PolyInter where
  fmap f i = PI (signature i) $ Map.map (fmap f) (interpretations i)

instance Functor (Polynomial V.Variable) where
  fmap f (Poly xs) = Poly $ map (fmap f) xs

instance Functor (Monomial V.Variable) where
  fmap f (Mono n vs) = Mono (f n) vs

instance (Num a, PrettyPrintable a, Eq a) => PrettyPrintable (PolyInter a) where
  pprint (PI sig ints) = columns [ (AlignRight, as), (AlignLeft, bs) ]
    where (as,bs) = unzip $ concatMap ppInter $ Map.toList ints
          ppInter (f,p) = [( brackets (pprint (f,sig)) <> fargs <+> char '=' <> text " ", pprint p)
                         , (text " ", text " ")
                        ]
            where fargs = parens $ hsep $ punctuate comma $ map (\i -> char 'x' <> int i) [1..a]
                  a = F.arity sig f                       


instance (Eq a, Num a, PrettyPrintable a) => PrettyPrintable (VPolynomial a) where 
  pprint p = pprintPolynomial p ppVar 
     where ppVar (V.Canon v) = char 'x' <> int v
           ppVar (V.User v)  = char 'y' <> int v

instance (Eq a, Num a, PrettyPrintable a) => PrettyPrintable (VPolynomial a, V.Variables) where 
  pprint (p,var) = pprintPolynomial p ppVar 
     where ppVar v = text $ V.variableName v var

pprintPolynomial :: (Eq a, Num a, PrettyPrintable a) => Polynomial t a -> (t -> Doc) -> Doc
pprintPolynomial (Poly ms) ppVar = hcat $ punctuate (text " + ") $ [ppMono  m |  m <- ms]
  where ppMono(Mono n []) = pprint n
        ppMono (Mono n pows) | n == 0 = empty
                             | n == 1 = ppPows pows
                             | otherwise = pprint n <> char '*' <> ppPows pows
        ppPows pows = hcat $ punctuate (char '*') $ map ppPow pows
        ppPow (Pow v e) | e == 1     = ppVar v
                        | otherwise = ppVar v <> char '^' <> int e

instance Show SimplePolyShape where
  show StronglyLinear = "strongly linear"
  show Linear         = "linear"
  show Simple         = "simple"
  show SimpleMixed    = "mixed"
  show Quadratic      = "quadratic"

instance AssocArgument PolyShape where
  assoc _ = [ ("linear", SimpleShape Linear)
            , ("stronglylinear", SimpleShape StronglyLinear)
            , ("simple", SimpleShape Simple)
            , ("simplemixed", SimpleShape SimpleMixed)              
            , ("quadratic", SimpleShape Quadratic)
            ]

instance Show PolyShape where
  show (SimpleShape s) = show s
  show (CustomShape _) = "custom shape"

instance (Eq a, Semiring a) => Interpretation (PolyInter a) (Polynomial V.Variable a) where
  interpretFun i f tis = bigPplus $ map handleMono fpoly
    where Poly fpoly = case Map.lookup f $ interpretations i of
                         Nothing -> error "Tct.Method.Poly.PolynomialInterpretation.interpretFun: function symbol not found in interpretation"
                         Just p  -> p
          handleMono (Mono n vs) = bigPprod $ constToPoly n : map handlePow vs
          handlePow (Pow (V.Canon v) e) | e <= 0    = constToPoly one
                                        | otherwise = handlePow' p p (e - (2 ^ (N.natToBits e - 1))) (N.natToBits e - 1)
            where p = tis !! (v - 1)
          handlePow (Pow (V.User _) _) = error "Tct.Method.Poly.PolynomialInterpretation.interpretFun: user defined variable in interpretation"
          handlePow' origp p e j | j > 0     = if e >= 2 ^ (j - 1)
                                               then handlePow' origp (origp `pprod` (p `pprod` p)) (e - (2 ^ (j - 1))) (j - 1)
                                               else handlePow' origp (p `pprod` p) e (j - 1)
                                 | otherwise = p
  interpretVar _ v     = varToPoly v

degrees :: PolyInter Int -> [(F.Symbol, Int)]
degrees pint = [(f, foldl max 0 [ maxdegree m | m <- monos])
               | (f,(Poly monos)) <- Map.toList $ interpretations $ pint ]
  where maxdegree (Mono 0 _)      = 0
        maxdegree (Mono _ powers) = foldl (+) 0 [e | Pow _ e <- powers]

toXml :: PolyInter Int -> PIKind -> UArgs.UsablePositions -> [Xml.XmlContent]
toXml pint knd uargs = tpe : [ inter f polys | (f,polys) <- Map.toList $ interpretations pint ]
  where sig = signature pint
        deg = foldl max 0 [ d | (_, d) <- degrees pint ]
        tpe = Xml.elt "type" []
               [Xml.elt "polynomialInterpretation" [] 
                 [ Xml.elt "domain" [] [Xml.elt "naturals" [] []]
                 , Xml.elt "degree" [] [Xml.int deg]
                 , Xml.elt "kind" [] 
                   [ case knd of 
                        UnrestrictedPoly _   -> Xml.elt "unrestricted" [] []
                        ConstructorBased _ _ -> Xml.elt "constructorBased" [] []
                   ]
                 , Xml.elt "shape" []
                   [ Xml.text $ show $ 
                     case knd of 
                       UnrestrictedPoly sp   -> sp
                       ConstructorBased _ sp -> sp ]
                 , UArgs.toXml sig uargs]]
        inter :: F.Symbol -> VPolynomial Int -> Xml.XmlContent
        inter f (Poly ms) =
          Xml.elt "interpret" []
           [ Xml.elt "name" [] [Xml.text $ F.symbolName sig f]
           , Xml.elt "arity" [] [Xml.int $ F.arity sig f] 
           , xsum $ [ xmono n vs | Mono n vs <- ms ]]
          
        xpoly p = Xml.elt "polynomial" [] [p]
        xsum = xpoly . Xml.elt "sum" []
        xprod = xpoly . Xml.elt "product" []

        xvar (V.Canon i) = xpoly $ Xml.elt "variable" [] [Xml.int i]
        xvar _           = error "non-canonical variable in abstract matrix interpretation"
        
        xelt e = xpoly $ Xml.elt "coefficient" [] [Xml.elt "integer" [] [Xml.int e]]
        xpow (Pow v i) = take i $ repeat $ xvar v
        xmono n [] = xprod [xelt n]
        xmono n vs = xprod $ xelt n : concatMap xpow vs

-- | @v ^^^ k@ denotes exponentiation of variable @v@ with constant @k@.
(^^^) :: a -> Int -> Power a
a ^^^ i = Pow a i

-- | Returns a new monomial without variables.
constant :: SimpleMonomial
constant = mono []

-- | @
-- mono [v1^^^k1,...,vn^^^kn]
-- @ 
-- constructs the 'SimpleMonomial'
-- @
-- c * v1^k1 * ... * v1^kn
-- @
-- where @c@ is unique for the constructed monomial.
mono :: [Power V.Variable] -> SimpleMonomial
mono = CoefficientMonomial

-- | Returns a new monomial whose coefficient is guaranteed to be @0@ or @1@.
boolCoefficient :: SimpleMonomial -> SimpleMonomial
boolCoefficient (CoefficientMonomial ps) = SimpleMonomial ps
boolCoefficient sm                       = sm

polynomialFromShape :: RingConst a => PolyShape -> (F.Symbol, Int) -> VPolynomial a
polynomialFromShape shape (f,ar) = mkPoly $ normalise $ monoFromShape shape
  where mkPoly monos = Poly $ [mkMono sm | sm <- monos]
          where mkMono (SimpleMonomial ps) = Mono (restrictvar $ PIVar True f ps) ps
                mkMono (CoefficientMonomial ps) = Mono (ringvar $ PIVar False f ps) ps
                                                  
        normalise = List.nubBy eqpowers
          where sm1 `eqpowers` sm2 = Set.fromList (smPowers sm1) == Set.fromList (smPowers sm2)
        
        monoFromShape (CustomShape mks) = mks vs
        monoFromShape (SimpleShape s) = 
          case s of 
            Linear         -> [ mono [v^^^1] | v <- vs] ++ [constant]
            StronglyLinear -> [ boolCoefficient $ mono [v^^^1] | v <- vs] ++ [constant]
            Simple         -> map mono $ foldr addvar [[]] vs
              where addvar v = concatMap (\vs' -> [vs', v^^^1:vs'])
            SimpleMixed    -> [ mono [v^^^2] | v <- vs ] ++ monoFromShape (SimpleShape Simple)
            Quadratic      -> map mono $ foldr addvar [[]] vs
              where addvar v = concatMap (\vs' -> [vs', v^^^1:vs',v^^^2:vs'])
        
        vs = [V.Canon i | i <- [1..ar]]
        

abstractInterpretation :: RingConst a => PIKind -> F.Signature -> PolyInter a
abstractInterpretation pk sig = PI sig $ Map.fromList $ map (\f -> (f, interpretf f)) $ Set.elems $ F.symbols sig
  where interpretf f = polynomialFromShape (getShape pk) (f,ar)
          where ar = F.arity sig f
                getShape (UnrestrictedPoly shape) = shape
                getShape (ConstructorBased cs shape) 
                  | f `Set.member` cs = SimpleShape StronglyLinear
                  | otherwise         = shape
