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
import Qlogic.PropositionalFormula
import Qlogic.Diophantine hiding (add)
import Qlogic.Semiring

import Termlib.Problem (Problem(..), StartTerms(..))
import Termlib.Trs (Trs)
import Termlib.Utils hiding (enum)
import qualified Termlib.Problem as Prob
import qualified Termlib.Rule as R
import qualified Termlib.Trs as Trs

import Tct.Encoding.AbstractInterpretation
import Tct.Encoding.Matrix
import Tct.Encoding.UsablePositions
import Tct.Processor.Args
import Tct.Processor.Args.Instances
import Tct.Processor.Orderings
import Tct.Utils.PPrint ()
import Tct.Method.Matrix.MatrixInterpretation hiding (signature)
import Tct.Method.Matrix.NaturalMI

import qualified Tct.Method.RuleSelector as RS
import qualified Tct.Processor.Args as A
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S

data WeightGap = WeightGap

data WgOn = WgOnTrs -- ^ Orient at least all non-DP rules.
          | WgOnAny -- ^ Orient some rule.
            deriving (Eq, Typeable, Bounded, Enum)

instance Show WgOn where
  show WgOnTrs = "trs"
  show WgOnAny = "any"

data WeightGapProof = 
  WeightGapProof { wgProof :: OrientationProof MatrixOrder
                 , wgConstGrowth :: Maybe Bool
                 }

instance PrettyPrintable WeightGapProof where
  pprint (WeightGapProof e@Empty _) = P.pprintProof e P.ProofOutput
  pprint (WeightGapProof p growth)
      | P.succeeded p = paragraph (show $ text "The weightgap principle applies"
                                          <+> parens (text "using the following" <+> text intertitle))
                        $+$ text ""
                        $+$ P.pprintProof p P.ProofOutput
                        $+$ text ""
                        $+$ text "The on-oriented rules are covered by the weightgap condition."
      | otherwise     = text "The weightgap principle does not apply."
    where intertitle = case growth of
                         Just False -> "nonconstant growth matrix-interpretation"
                         Just True  -> "constant growth matrix-interpretation"
                         Nothing    -> "matrix-interpretation"

instance P.ComplexityProof WeightGapProof where 
  answer = P.answer . wgProof
  pprintProof order _ = pprint order

instance S.Processor WeightGap where
  name WeightGap = "weightgap"
  instanceName inst = 
    show $ text "weightgap" 
           -- <+> case wgon of { WgOnTrs -> text "on strict TRS" ; _ -> PP.empty}
           <+> text "of dimension" <+> pprint wgDim
           <> maybet wgDeg (\ deg -> text ", maximal degree" <+> pprint deg)
           <> maybet wgBits (\ bnd -> text ", bits" <+> pprint bnd)
           <> maybet wgCbits (\ cbs -> text ", cbits" <+> pprint cbs)
           <> (if ua then PP.empty else text ", without usable arguments")
      where  _ :+: _ :+: wgDeg :+: wgDim :+: _ :+: wgBits :+: wgCbits :+: ua = S.processorArgs inst
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
                          
  solve inst prob = mkProof `liftM` orientWG rs (Prob.sanitise prob) wargs
    where rs = RS.rsSelect (RS.selAllOf RS.selStricts) prob
          wargs@(wgon :+: _) = S.processorArgs inst
          mkProof p = WeightGapProof { wgProof = p
                                     , wgConstGrowth  = Just $ Trs.isEmpty (strictTrs prob) || wgon == WgOnTrs }
  solvePartial inst rs prob = mkProof `liftM` orientWG rs (Prob.sanitise prob) wargs
    where wargs@(wgon :+: _) = S.processorArgs inst
          mkProof p = 
            P.PartialProof { P.ppInputProblem = prob
                           , P.ppResult       = WeightGapProof { wgProof = p
                                                               , wgConstGrowth  = Just $ Trs.isEmpty (strictTrs prob) || wgon == WgOnTrs }
                           , P.ppRemovableDPs = rdps
                           , P.ppRemovableTrs = rtrs }
                   where (rdps,rtrs) = 
                           case p of 
                             (Order ord) -> let mi = ordInter ord 
                                            in ( Trs.toRules $ strictRules mi $ Prob.dpComponents prob
                                               , Trs.toRules $ strictRules mi $ Prob.trsComponents prob)
                             _ -> ([], [])
                           

data Orientation = OrientStrict R.Rule
                 deriving (Eq, Ord, Show, Typeable)
instance PropAtom Orientation

orientWGConstraints :: (Eq l) => MatrixInter (DioPoly DioVar Int) -> Trs -> DioFormula l DioVar Int
orientWGConstraints absmi sr = bigAnd [ ruleConstraint rl | rl <- Trs.toRules sr ]
  where ruleConstraint rl = wgConstraint 
                            && (dioAtom (OrientStrict rl) --> orientConstraint)
          where li = interpretTerm absmi (R.lhs rl)
                ri = interpretTerm absmi (R.rhs rl)
                d  = dimension absmi 
                
                wgConstraint = 
                  bigAnd [ maybe bot (\ lm -> row 1 lm .>=. row 1 rm) (Map.lookup v $ coefficients li)
                         | (v,rm) <- Map.toList $ coefficients ri]
                orientConstraint = 
                  bigAnd [ maybe bot (\ lm -> bigAnd [ row j lm .>=. row j rm | j <- [2..d] ]) 
                             (Map.lookup v $ coefficients li)
                         | (v,rm) <- Map.toList $ coefficients ri]
                  && constant li .>. constant ri


orientWG :: P.SolverM m => P.SelectorExpression -> Problem -> Domains (S.ArgumentsOf WeightGap) -> m (OrientationProof MatrixOrder)
orientWG rs prob (wgon :+: wgp@(wgKind :+: wgDeg :+: as)) = 
    solveConstraint prob ua mk sig mp $ 
      RS.onSelectedRequire rs' (\ _ rl -> dioAtom (OrientStrict rl))
      && orientWGConstraints absmi sr
      && weakTrsConstraints absmi wr
      && slmiSafeRedpairConstraints sig ua absmi 
      && uargMonotoneConstraints ua absmi 
      && kindConstraints mk absmi
      
  where sig = Prob.signature prob
        mp = miKnd :+: deg :+: as
        absmi = abstractInterpretation mk d sig :: MatrixInter (DioPoly DioVar Int)
        d = dim mp        
        
        rs' | wgon == WgOnTrs = RS.BigAnd $ rs : [  RS.SelectTrs r | r <- Trs.rules strs]
            | otherwise = rs

        miKnd | Trs.isEmpty strs || wgon == WgOnTrs = wgKind
              | wgKind == Unrestricted = Algebraic
              | otherwise = wgKind
                            
        deg | Trs.isEmpty strs || wgon == WgOnTrs = wgDeg
            | otherwise = Just 1
        
        ua = case Prob.startTerms prob of
              BasicTerms {} 
                | isUargsOn wgp -> usableArgs (strategy prob) allrules
              _ -> fullWithSignature (signature prob)
              
        mk = kind mp st
           where st | Trs.isEmpty strs || wgon == WgOnTrs = startTerms prob
                    | otherwise = toTA $ startTerms prob
                 toTA (BasicTerms ds cs) = TermAlgebra $ ds `Set.union` cs
                 toTA st'                = st'

        sr = Prob.strictComponents prob
        wr = Prob.weakComponents prob
        strs = Prob.strictTrs prob
        allrules = Prob.allComponents prob


weightgapProcessor :: S.StdProcessor WeightGap
weightgapProcessor = S.StdProcessor WeightGap
