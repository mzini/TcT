{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{- | 
Module      :  Tct.Method.Weightgap
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Andreas Schnabl <andreas.schnabl@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

This module defines the weight gap processor.
-}



module Tct.Method.Weightgap where

import Control.Monad (liftM)
import Prelude hiding ((&&), (||))
import Text.PrettyPrint.HughesPJ hiding (empty)
import qualified Text.PrettyPrint.HughesPJ as PP
import Data.Typeable
import qualified Data.Map as Map
import qualified Data.Set as Set

import Qlogic.Boolean
import Qlogic.Diophantine hiding (add)
import Qlogic.Semiring

import Termlib.Problem (Problem(..), StartTerms(..), strictComponents)
import Termlib.Rule (Rule(..))
import Termlib.Trs (Trs)
import Termlib.Utils hiding (enum)
import qualified Termlib.Problem as Prob
import qualified Termlib.Rule as R
import qualified Termlib.Trs as Trs
import Termlib.Trs.PrettyPrint (pprintNamedTrs)

import Tct.Certificate (add, certified, unknown, upperBound)
import Tct.Encoding.AbstractInterpretation
import Tct.Encoding.Matrix
import Tct.Encoding.UsablePositions
import Tct.Processor.Args
import Tct.Processor.Args.Instances
import Tct.Processor.Orderings
import Tct.Utils.Enum (enumeration')
import Tct.Utils.PPrint ()
import Tct.Method.Matrix.MatrixInterpretation hiding (signature)
import Tct.Method.Matrix.NaturalMI
import qualified Tct.Processor.Args as A
import qualified Tct.Processor as P
import qualified Tct.Processor.Transformations as T

data WeightGap = WeightGap

data WgOn = WgOnTrs -- ^ Orient at least all non-DP rules.
          | WgOnAny -- ^ Orient some rule.
            deriving (Eq, Typeable, Bounded, Enum)

instance Show WgOn where
  show WgOnTrs = "trs"
  show WgOnAny = "any"

data WeightGapProof = WeightGapProof { wgInputProblem :: Problem
                                     , wgProof :: OrientationProof MatrixOrder
                                     , wgRemovableDps :: [Rule]
                                     , wgRemovableTrs :: [Rule]
                                     , wgConstGrowth :: Maybe Bool
                                     }

instance PrettyPrintable WeightGapProof where
  pprint (WeightGapProof _ e@Empty _ _ _) = P.pprintProof e P.ProofOutput
  pprint wgp 
      | P.succeeded p = paragraph ("The weightgap principle applies.")
                        $+$ text ""
                        $+$ P.pprintProof p P.ProofOutput
                        $+$ text ""
                        $+$ paragraph ("This " ++ intertitle ++ " orients following rules strictly:")

                        $+$ pptrs "DPs" sDPs
                        $+$ pptrs "Trs" sTrs
                        $+$ text ""
                        $+$ paragraph "The rules moved into the corresponging weak component."
      | otherwise     = text "The weightgap principle does not apply."
    where ip = wgInputProblem wgp
          p  = wgProof wgp
          sDPs = Trs.fromRules $ wgRemovableDps wgp
          sTrs = Trs.fromRules $ wgRemovableTrs wgp
          pptrs = pprintNamedTrs sig vars
          sig  = signature ip
          vars = variables ip
          intertitle = case wgConstGrowth wgp of
                         Just False -> "nonconstant growth matrix-interpretation"
                         Just True  -> "constant growth matrix-interpretation"
                         Nothing    -> "matrix-interpretation"

instance T.TransformationProof WeightGap where 
  answer proof = case T.subProofs proof of 
                     [(_,subproof)] -> mkAnswer (P.answer wgproof) (P.answer subproof)
                     _              -> P.MaybeAnswer
    where wgproof = wgProof $ T.transformationProof proof
          mkAnswer (P.CertAnswer tc) (P.CertAnswer c) = P.CertAnswer $ certified (unknown, add (upperBound tc) (upperBound c))
          mkAnswer _                 a                = a
                       
  pprintTProof _ _ p _ = pprint p


instance T.Transformer WeightGap where
  name WeightGap = "weightgap"
  instanceName (T.TheTransformer _ as) = show $ text "weightgap" 
                                                <+> case wgon of { WgOnTrs -> text "on strict TRS" ; _ -> PP.empty}
                                                <+> text "of dimension" <+> text (show wgDim)
                                                <> maybet wgDeg (\ deg -> text ", maximal degree" <+> pprint deg)
                                                <> maybet wgBits (\ bnd -> text ", bits" <+> pprint bnd)
                                                <> maybet wgCbits (\ cbs -> text ", cbits" <+> pprint cbs)
                                                <> (if ua then PP.empty else text ", without usable arguments")
      where  wgon :+: _ :+: wgDeg :+: wgDim :+: _ :+: wgBits :+: wgCbits :+: ua = as
             maybet Nothing  _ = PP.empty
             maybet (Just p) f = f p
  description WeightGap = [ "Uses the weight gap principle to shift some strict rules to the weak part of the problem." ]

  type ArgumentsOf WeightGap = (Arg (EnumOf WgOn)) :+: MatrixOptions
  type ProofOf WeightGap = WeightGapProof
  arguments WeightGap =   opt { A.name        = "on"
                              , A.description = unlines [ "This flag determine which rules have to be strictly oriented by the the matrix interpretation for"
                                                        , "the weight gap principle. Here 'trs' refers to all strict non-dependency-pair rules of the"
                                                        , "considered problem, while 'any' only demands any rule at all to be strictly oriented."
                                                        , "The default value is 'trs'."
                                                        ]
                              , A.defaultValue = WgOnTrs}
                          :+: matrixOptions
  transform inst prob 
     | Trs.isEmpty $ strictComponents prob = 
          return $ T.NoProgress $ WeightGapProof { wgInputProblem = prob
                                                 , wgProof        = Empty
                                                 , wgRemovableDps = []
                                                 , wgRemovableTrs = []
                                                 , wgConstGrowth  = Nothing }
     | otherwise = mkProof `liftM` orientWG (Prob.sanitise prob) targs
           where targs@(wgon :+: _) = T.transformationArgs inst
                 mkProof p@(Order ord) 
                   | Trs.isEmpty remdps && Trs.isEmpty remtrs = T.NoProgress wgpr
                   | otherwise = T.Progress wgpr (enumeration' [prob'])
                   where wgpr   = WeightGapProof { wgInputProblem = prob
                                                 , wgProof        = p
                                                 , wgRemovableDps = Trs.toRules remdps
                                                 , wgRemovableTrs = Trs.toRules remtrs
                                                 , wgConstGrowth  = Just $ Trs.isEmpty (strictTrs prob) || wgon == WgOnTrs }
                         mi = ordInter ord
                         remdps = strictRules mi $ strictDPs prob
                         remtrs = strictRules mi $ strictTrs prob
                         prob'  = prob { strictDPs = strictDPs prob Trs.\\ remdps
                                       , strictTrs = strictTrs prob Trs.\\ remtrs
                                       , weakDPs   = weakDPs prob `Trs.union` remdps
                                       , weakTrs   = weakTrs prob `Trs.union` remtrs }
                 mkProof p = T.NoProgress WeightGapProof { wgInputProblem = prob
                                                         , wgProof        = p
                                                         , wgRemovableDps = []
                                                         , wgRemovableTrs = []
                                                         , wgConstGrowth  = Nothing }
                 

orientWG :: P.SolverM m => Problem -> Domains (T.ArgumentsOf WeightGap) -> m (OrientationProof MatrixOrder)
orientWG prob (wgon :+: wgp@(wgKind :+: wgDeg :+: as)) = 
    solveConstraint ua st sig mp $ 
      strictWGConstraints sr absmi 
      && wgonConstraints wgon 
      && weakTrsConstraints absmi wr
      && slmiSafeRedpairConstraints sig ua absmi 
      && uargMonotoneConstraints ua absmi 
      && kindConstraints knd absmi
      
  where mp = miKnd :+: deg :+: as
        absmi      = abstractInterpretation knd (dim mp) sig :: MatrixInter (DioPoly DioVar Int)
        miKnd | Trs.isEmpty sr || wgon == WgOnTrs = wgKind
              | wgKind == Unrestricted = Algebraic
              | otherwise = wgKind
        deg | Trs.isEmpty sr || wgon == WgOnTrs = wgDeg
            | otherwise = Just 1
        sig = Prob.signature prob
        st | Trs.isEmpty sr || wgon == WgOnTrs = startTerms prob
           | otherwise = toTA $ startTerms prob
          where toTA (BasicTerms ds cs) = TermAlgebra $ ds `Set.union` cs
                toTA st'                 = st'
        ua = case Prob.startTerms prob of
              BasicTerms {} 
                | isUargsOn wgp -> usableArgs (strategy prob) allrules
              _ -> fullWithSignature (signature prob)
        knd = kind mp st

        wgonConstraints WgOnTrs = strictTrsConstraints absmi nondup
        wgonConstraints WgOnAny | Trs.isEmpty sr = top 
                                | otherwise      = strictOneConstraints absmi sr
        sr = Prob.strictComponents prob
        wr = Prob.weakComponents prob
        nondup = Prob.strictTrs prob
        allrules = Prob.allComponents prob

strictWGConstraints :: (AbstrOrdSemiring a b, MIEntry a) => Trs -> MatrixInter a -> b
strictWGConstraints trs mi = trsConstraints f mi trs
  where f li ri = bigAnd (zipWith coeffConstraint (Map.elems $ coefficients li) (Map.elems $ coefficients ri))
        coeffConstraint lm rm = row 1 lm .>=. row 1 rm

nondupConstraints :: (AbstrOrdSemiring a b, MIEntry a) => Rule -> MatrixInter a -> b
nondupConstraints r mi = bigAnd $ zipWith coeffConstraint (Map.elems $ coefficients $ interpretTerm mi $ R.lhs r) (Map.elems $ coefficients $ interpretTerm mi $ R.rhs r)
  where coeffConstraint lm rm = row 1 lm .>=. row 1 rm

weightgapProcessor :: T.Transformation WeightGap P.AnyProcessor
weightgapProcessor = T.Transformation WeightGap
