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
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Tct.Method.Poly.NaturalPI where

import Prelude hiding (not)

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Typeable
import Text.PrettyPrint.HughesPJ

import Qlogic.Boolean
import qualified Qlogic.NatSat as N
import Qlogic.Semiring

import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Problem as Prob
import qualified Termlib.Rule as R
import qualified Termlib.Trs as Trs
import Termlib.Utils
import qualified Termlib.Variable as V

import Tct.Certificate (poly, expo, certified, unknown)
import Tct.Encoding.Polynomial
import Tct.Encoding.UsablePositions hiding (empty)
import Tct.Method.Poly.PolynomialInterpretation
import Tct.Processor (Answerable(..), Verifiable(..), Answer(..), ComplexityProof)
import Tct.Processor.Args
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances
import Tct.Processor.Orderings
import Tct.Processor.PPrint (indent)
import qualified Tct.Processor.Standard as S

data PolynomialOrder = PolynomialOrder { ordInter :: PolyInter Int
                                       , param    :: PIKind
                                       , uargs    :: UsablePositions } deriving Show

data NaturalPI = NaturalPI deriving (Typeable, Show)

instance PrettyPrintable PolynomialOrder where
  pprint order = (if uargs order == fullWithSignature (signature $ ordInter order)
                  then empty
                  else (text "The following argument positions are usable:")
                  $+$ indent (pprint (uargs order, signature $ ordInter order)))
                 $+$ (text "We have the following" <+> ppknd (param order) <+> text "polynomial interpretation:")
                 $+$ pprint (ordInter order)
    where ppknd (UnrestrictedPoly   shp) = ppshp shp
          ppknd (ConstructorBased _ shp) = text "restricted" <+> ppshp shp
          ppshp StronglyLinear = text "strongly linear"
          ppshp Linear = text "linear"
          ppshp Simple = text "simple"
          ppshp SimpleMixed = text "simple-mixed"
          ppshp Quadratic = text "quadratic"

instance Answerable PolynomialOrder where
  answer (PolynomialOrder _ (UnrestrictedPoly   StronglyLinear) _) = CertAnswer $ certified (unknown, poly (Just 1))
  answer (PolynomialOrder _ (UnrestrictedPoly   Linear)         _) = CertAnswer $ certified (unknown, expo (Just 1))
  answer (PolynomialOrder _ (UnrestrictedPoly   Simple)         _) = CertAnswer $ certified (unknown, expo (Just 1))
  answer (PolynomialOrder _ (UnrestrictedPoly   SimpleMixed)    _) = CertAnswer $ certified (unknown, expo (Just 2))
  answer (PolynomialOrder _ (UnrestrictedPoly   Quadratic)      _) = CertAnswer $ certified (unknown, expo (Just 2))
  answer (PolynomialOrder _ (ConstructorBased _ StronglyLinear) _) = CertAnswer $ certified (unknown, poly (Just 1))
  answer (PolynomialOrder _ (ConstructorBased _ Linear)         _) = CertAnswer $ certified (unknown, poly (Just 1))
  answer (PolynomialOrder i (ConstructorBased _ Simple)         _) = CertAnswer $ certified (unknown, poly (Just a))
    where a = maximum [ F.arity sig f | f <- Set.elems (F.symbols sig) ]
          sig = signature i
  answer (PolynomialOrder i (ConstructorBased _ SimpleMixed)    _) = CertAnswer $ certified (unknown, poly (Just a))
    where a = maximum $ 2:[ F.arity sig f | f <- Set.elems (F.symbols sig) ]
          sig = signature i
  answer (PolynomialOrder i (ConstructorBased _ Quadratic)      _) = CertAnswer $ certified (unknown, poly (Just a))
    where a = 2 * maximum [ F.arity sig f | f <- Set.elems (F.symbols sig) ]
          sig = signature i

instance Verifiable PolynomialOrder
instance ComplexityProof PolynomialOrder

instance S.Processor NaturalPI where
  name NaturalPI = "poly"

  description NaturalPI = [ "This processor orients the problem using polynomial interpretation over natural numbers." ]

  type S.ArgumentsOf NaturalPI = (Arg (EnumOf PolyShape)) :+: (Arg Nat) :+: (Arg (Maybe Nat)) :+: (Arg (Maybe Nat)) :+: (Arg Bool)
  arguments NaturalPI = opt { A.name         = "kind"
                            , A.description  = unlines [ "This argument specifies the shape of the polynomials used in the interpretation."
                                                       , "Allowed values are 'stronglylinear', 'linear', 'simple', 'simplemixed', and 'quadratic',"
                                                       , "referring to the respective shapes of the abstract polynomials used."
                                                       , "The deault value is 'stronglylinear'." ]
                            , A.defaultValue = StronglyLinear }
                        :+:
                        opt { A.name        = "bound"
                            , A.description = unlines [ "This argument specifies an upper-bound on coefficients appearing in the interpretation."
                                                      , "Such an upper-bound is necessary as we employ bit-blasting to SAT internally"
                                                      , "when searching for compatible matrix interpretations."]
                            , A.defaultValue = Nat 3 }
                        :+:
                        opt { A.name        = "bits"
                            , A.description = unlines [ "This argument plays the same role as 'bound',"
                                                      , "but instead of an upper-bound the number of bits is specified."
                                                      , "This argument overrides the argument 'bound'."]
                            , A.defaultValue = Nothing }
                        :+:
                        opt { A.name        = "cbits"
                            , A.description = unlines [ "This argument specifies the number of bits used for intermediate results, "
                                                      , "as for instance coefficients of matrices obtained by interpreting"
                                                      , "left- and right-hand sides."]
                            , A.defaultValue = Nothing }
                        :+:
                        opt { A.name        = "uargs"
                            , A.description = unlines [ "This argument specifies whether usable arguments are computed (if applicable)"
                                                      , "in order to relax the monotonicity constraints on the interpretation."]
                            , A.defaultValue = True }

  instanceName inst = show (shape $ S.processorArgs inst) ++ " polynomial interpretation"

  type S.ProofOf NaturalPI = OrientationProof PolynomialOrder

  solve inst problem | Trs.isEmpty (Prob.strictTrs problem) = undefined
                     | otherwise                            = undefined

  solvePartial inst oblrules problem | Trs.isEmpty (Prob.strictTrs problem) = undefined
                                     | otherwise                            = undefined

polyProcessor :: S.StdProcessor NaturalPI
polyProcessor = S.StdProcessor NaturalPI

-- argument accessors

kind :: Domains (S.ArgumentsOf NaturalPI) -> Prob.StartTerms -> PIKind
kind args st = kind' (shape args) st
  where kind' shp Prob.TermAlgebra       = UnrestrictedPoly shp
        kind' shp (Prob.BasicTerms _ cs) = ConstructorBased cs shp

shape :: Domains (S.ArgumentsOf NaturalPI) -> PolyShape
shape (shp :+: _ :+: _ :+: _ :+: _) = shp

bound :: Domains (S.ArgumentsOf NaturalPI) -> N.Size
bound (_ :+: Nat bnd :+: mbits :+: _ :+: _) = case mbits of
                                                Just (Nat b) -> N.Bits b
                                                Nothing      -> N.Bound bnd

cbits :: Domains (S.ArgumentsOf NaturalPI) -> Maybe N.Size
cbits (_ :+: _ :+: _ :+: b :+: _) = do Nat n <- b
                                       return $ N.Bits n

isUargsOn :: Domains (S.ArgumentsOf NaturalPI) -> Bool
isUargsOn (_ :+: _ :+: _ :+: _ :+: ua) = ua

usableArgsWhereApplicable :: PolyDP -> F.Signature -> Prob.StartTerms -> Bool -> Prob.Strategy -> Trs.Trs -> Trs.Trs -> UsablePositions
usableArgsWhereApplicable PWithDP sig _                     ua strat r s = (if ua then restrictToSignature compSig (usableArgs strat r s) else fullWithSignature compSig) `union` emptyWithSignature nonCompSig
  where compSig    = F.restrictToSymbols sig $ Set.filter (F.isCompound sig) $ F.symbols sig
        nonCompSig = F.restrictToSymbols sig $ Set.filter (not . F.isCompound sig) $ F.symbols sig
usableArgsWhereApplicable PNoDP   sig Prob.TermAlgebra      _  _     _ _ = fullWithSignature sig
usableArgsWhereApplicable PNoDP   sig (Prob.BasicTerms _ _) ua strat r s = if ua then usableArgs strat r s else fullWithSignature sig

data PolyDP = PWithDP | PNoDP deriving Show
data PolyRelativity = PDirect | PRelative [R.Rule] deriving Show

monotoneConstraints :: AbstrOrdSemiring a b => PolyInter a -> b
monotoneConstraints i = bigAnd $ Map.mapWithKey handlefun $ interpretations i
  where sig = signature i
        handlefun f p = bigAnd $ map (\n -> getCoeff [Pow (V.Canon n) 1] p .>=. one) [1..F.arity sig f]
