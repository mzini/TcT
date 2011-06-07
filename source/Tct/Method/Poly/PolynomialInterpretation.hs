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

module Tct.Method.Poly.PolynomialInterpretation where

import Data.Typeable
import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ

import Qlogic.PropositionalFormula
import Qlogic.Semiring

import Termlib.Utils
import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Variable as V

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
               deriving Show

data PIKind = UnrestrictedPoly PolyShape
            | ConstructorBased (Set.Set F.Symbol) PolyShape
            deriving Show

instance PropAtom PIVar

instance PrettyPrintable a => PrettyPrintable (PolyInter a) where
  pprint (PI sig ints) = (text "Interpretation Functions:" $$ (nest 1 $ printInters ints))
    where printInters = vcat . map (uncurry printInter) . Map.assocs
          printInter f p = fHead <+> nest (length (show fHead) + 1) (pprint p)
            where fHead = pprint (f,sig) <> fargs <+> char '='
                  fargs = parens $ hsep $ punctuate comma $ map (\i -> char 'x' <> int i) [1..a]
                  a = F.arity sig f

instance PrettyPrintable a => PrettyPrintable (Polynomial V.Variable a) where
  pprint (Poly xs) = hsep $ punctuate (text " + ") $ map pprint xs

instance PrettyPrintable a => PrettyPrintable (Monomial V.Variable a) where
  pprint (Mono n vs) = pprint n <> char '*' <> hsep (punctuate (char '*') $ map pprint vs)

instance PrettyPrintable (Power V.Variable) where
  pprint (Pow (V.Canon v) e) = char 'x' <> int v <> char '^' <> int e
  pprint (Pow (V.User  v) e) = char 'y' <> int v <> char '^' <> int e

stronglyLinearPolynomial :: RingConst a => F.Symbol -> F.Signature -> VPolynomial a
stronglyLinearPolynomial f sig = Poly $ foldr (\i p -> ithmono i:p) [Mono (ringvar $ PIVar True f []) []] [1..a]
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
