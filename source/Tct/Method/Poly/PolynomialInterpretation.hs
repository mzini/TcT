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

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Tct.Method.Poly.PolynomialInterpretation where

import Data.Typeable
import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ

import qualified Qlogic.NatSat as N
import Qlogic.PropositionalFormula
import Qlogic.Semiring

import Termlib.Utils
import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Variable as V

import Tct.Encoding.HomomorphicInterpretation
import Tct.Encoding.Polynomial

data PolyInter a = PI { signature :: F.Signature
                      , interpretations :: Map.Map F.Symbol (VPolynomial a) }
                      deriving Show

data PIVar = PIVar { restrict :: Bool
                   , varfun :: F.Symbol
                   , argpos :: [Power V.Variable] }
                   deriving (Eq, Ord, Show, Typeable)

type VPolynomial a = Polynomial V.Variable a
type VMonomial a = Monomial V.Variable a

data PolyShape = StronglyLinear
               | Linear
               | Simple
               | SimpleMixed
               | Quadratic
               deriving (Typeable, Bounded, Enum)

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

instance PrettyPrintable a => PrettyPrintable (PolyInter a) where
  pprint (PI sig ints) = (text "Interpretation Functions:" $$ (nest 1 $ printInters ints))
    where printInters = vcat . map (uncurry printInter) . Map.assocs
          printInter f p = fHead <+> nest (length (show fHead) + 1) (pprint p)
            where fHead = pprint (f,sig) <> fargs <+> char '='
                  fargs = parens $ hsep $ punctuate comma $ map (\i -> char 'x' <> int i) [1..a]
                  a = F.arity sig f

instance PrettyPrintable a => PrettyPrintable (Polynomial V.Variable a) where
  pprint (Poly xs) = hcat $ punctuate (text " + ") $ map pprint xs

instance PrettyPrintable a => PrettyPrintable (Monomial V.Variable a) where
  pprint (Mono n []) = pprint n
  pprint (Mono n vs) = pprint n <> char '*' <> hcat (punctuate (char '*') $ map pprint vs)

instance PrettyPrintable (Power V.Variable) where
  pprint (Pow (V.Canon v) e) = char 'x' <> int v <> if e == 1 then empty else char '^' <> int e
  pprint (Pow (V.User  v) e) = char 'y' <> int v <> if e == 1 then empty else char '^' <> int e

instance Show PolyShape where
  show StronglyLinear = "stronglylinear"
  show Linear         = "linear"
  show Simple         = "simple"
  show SimpleMixed    = "smixed"
  show Quadratic      = "quadratic"

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

stronglyLinearPolynomial :: RingConst a => F.Symbol -> F.Signature -> VPolynomial a
stronglyLinearPolynomial f sig = Poly $ foldr (\i p -> ithmono i:p) [Mono (ringvar $ PIVar False f []) []] [1..a]
  where a = F.arity sig f
        ithmono i = Mono (restrictvar $ PIVar True f [Pow (V.Canon i) 1]) [Pow (V.Canon i) 1]

linearPolynomial :: RingConst a => F.Symbol -> F.Signature -> VPolynomial a
linearPolynomial f sig = Poly $ foldr (\i p -> ithmono i:p) [Mono (ringvar $ PIVar False f []) []] [1..a]
  where a = F.arity sig f
        ithmono i = Mono (ringvar $ PIVar False f [Pow (V.Canon i) 1]) [Pow (V.Canon i) 1]

simplePolynomial :: RingConst a => F.Symbol -> F.Signature -> VPolynomial a
simplePolynomial f sig = Poly $ foldr additharg [Mono (ringvar $ PIVar False f []) []] [1..a]
  where a = F.arity sig f
        additharg i p = concatMap (\(Mono n vs) -> [Mono n vs, Mono (ringvar $ PIVar False f $ Pow (V.Canon i) 1:vs) $ Pow (V.Canon i) 1:vs]) p

simpleMixedPolynomial :: RingConst a => F.Symbol -> F.Signature -> VPolynomial a
simpleMixedPolynomial f sig = Poly $ foldr (\i p -> ithmono i:p) subresult [1..a]
  where a = F.arity sig f
        Poly subresult = simplePolynomial f sig
        ithmono i = Mono (ringvar $ PIVar False f [Pow (V.Canon i) 2]) [Pow (V.Canon i) 2]

quadraticPolynomial :: RingConst a => F.Symbol -> F.Signature -> VPolynomial a
quadraticPolynomial f sig = Poly $ foldr additharg [Mono (ringvar $ PIVar False f []) []] [1..a]
  where a = F.arity sig f
        additharg i p = concatMap (\(Mono n vs) -> [Mono n vs, addedMono i vs 1, addedMono i vs 2]) p
        addedMono i vs e = Mono (ringvar $ PIVar False f $ Pow (V.Canon i) e:vs) $ Pow (V.Canon i) e:vs

abstractInterpretation :: RingConst a => PIKind -> F.Signature -> PolyInter a
abstractInterpretation pk sig = PI sig $ Map.fromList $ map (\f -> (f, interpretf f)) $ Set.elems $ F.symbols sig
  where interpretf f = case pk of
                         UnrestrictedPoly shape    -> op shape f sig
                         ConstructorBased cs shape -> if f `Set.member` cs
                                                      then stronglyLinearPolynomial f sig
                                                      else op shape f sig
        op shape = case shape of
                     StronglyLinear -> stronglyLinearPolynomial
                     Linear -> linearPolynomial
                     Simple -> simplePolynomial
                     SimpleMixed -> simpleMixedPolynomial
                     Quadratic -> quadraticPolynomial
