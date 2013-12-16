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
import Tct.Utils.Enum (enumeration')

import qualified Tct.Method.RuleSelector as RS
import qualified Tct.Processor.Args as A
import qualified Tct.Processor as P
import qualified Tct.Proof as Proof
import qualified Tct.Processor.Transformations as T
import qualified Tct.Certificate as Cert
import Tct.Processor (certificate)

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
                        $+$ text "Further, it can be verified that all rules not oriented are covered by the weightgap condition."
      | otherwise     = text "The weightgap principle does not apply."
    where intertitle = case growth of
                         Just False -> "nonconstant growth matrix-interpretation"
                         Just True  -> "constant growth matrix-interpretation"
                         Nothing    -> "matrix-interpretation"

instance T.TransformationProof WeightGap where 
  answer proof = mkAnswer (T.answerFromSubProof proof) (P.answer $ wgProof tProof)
    where 
      tProof = T.transformationProof proof
      mkAnswer a1 a2 = 
        case ub of 
          Cert.Unknown -> P.MaybeAnswer 
          _ -> P.CertAnswer $ Cert.certified (Cert.constant, ub)
        where 
          ub = ubound a1 `Cert.add` ubound a2
          ubound = Cert.upperBound . certificate
          
  pprintTProof _ _ tproof _ = pprint tproof

  tproofToXml _ _ tproof = ( "weightgap"
                           , [Proof.toXml (wgProof tproof)])

instance T.Transformer WeightGap where
  name WeightGap = "weightgap"
  instanceName inst = 
    show $ text "weightgap" 
           -- <+> case wgon of { WgOnTrs -> text "on strict TRS" ; _ -> PP.empty}
           <+> text "of dimension" <+> pprint wgDim
           <> maybet wgDeg (\ deg -> text ", maximal degree" <+> pprint deg)
           <> maybet wgBits (\ bnd -> text ", bits" <+> pprint bnd)
           <> maybet wgCbits (\ cbs -> text ", cbits" <+> pprint cbs)
           <> (if ua then PP.empty else text ", without usable arguments")
      where  _ :+: _ :+:  _ :+: wgDeg :+: wgDim :+: _ :+: wgBits :+: wgCbits :+: ua :+: _ = T.transformationArgs inst
             maybet Nothing  _ = PP.empty
             maybet (Just p) f = f p
  description WeightGap = [ "Uses the weight gap principle to shift some strict rules to the weak part of the problem." ]

  type ArgumentsOf WeightGap = Arg (EnumOf WgOn) :+: Arg (Assoc RS.ExpressionSelector) :+: MatrixOptions
  type ProofOf WeightGap = WeightGapProof
  arguments WeightGap =   
    opt { A.name        = "on"
        , A.description = unlines [ "This flag determine which rules have to be strictly oriented by the the matrix interpretation for"
                                  , "the weight gap principle. Here 'trs' refers to all strict non-dependency-pair rules of the"
                                  , "considered problem, while 'any' only demands any rule at all to be strictly oriented."
                                  , "The default value is 'trs'."]
        , A.defaultValue = WgOnTrs}
    :+: 
    opt { A.name         = "split" 
        , A.defaultValue = RS.selAnyOf RS.selStricts
        , A.description  = unwords 
                           [ "This argument determines which rules should be oriented."]
        }
    :+: matrixOptions
                          
  transform inst prob = mkProof `liftM` orientWG (Prob.sanitise prob) wargs
    where 
      wargs@(wgon :+: _) = T.transformationArgs inst
      mkProof p 
        | Trs.isEmpty oriented = T.NoProgress $ tproof
        | otherwise = T.Progress tproof $ enumeration' [subproblem]
        where 
          tproof = WeightGapProof { wgProof = p
                                  , wgConstGrowth  = Just $ Trs.isEmpty (strictTrs prob) || wgon == WgOnTrs }
          (dps,trs) = 
            case p of 
              (Order ord) -> let mi = ordInter ord 
                             in ( strictRules mi $ Prob.dpComponents prob
                                , strictRules mi $ Prob.trsComponents prob)
              _ -> (Trs.empty, Trs.empty)                   

          oriented = dps `Trs.union` trs
                           
          subproblem = 
            prob { Prob.strictDPs = sDps
                 , Prob.strictTrs = sTrs
                 , Prob.weakTrs   = rTrs `Trs.union` weakTrs prob
                 , Prob.weakDPs   = rDps `Trs.union` weakDPs prob }
            where 
              rDps = dps `Trs.intersect` Prob.strictDPs prob
              rTrs = trs `Trs.intersect` Prob.strictTrs prob
              sDps = Prob.strictDPs prob Trs.\\ rDps
              sTrs = Prob.strictTrs prob Trs.\\ rTrs
              
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


orientWG :: P.SolverM m => Problem -> Domains (T.ArgumentsOf WeightGap) -> m (OrientationProof MatrixOrder)
orientWG prob (wgon :+: rs :+: wgp@(wgKind :+: wgDeg :+: as)) = 
    solveConstraint prob ua mk sig mp $ 
      RS.onSelectedRequire se' (\ _ rl -> dioAtom (OrientStrict rl))
      && orientWGConstraints absmi sr
      && weakTrsConstraints absmi wr
      && slmiSafeRedpairConstraints sig ua absmi 
      && uargMonotoneConstraints ua absmi 
      && kindConstraints mk absmi
      
  where sig = Prob.signature prob
        mp = miKnd :+: deg :+: as
        absmi = abstractInterpretation mk d sig :: MatrixInter (DioPoly DioVar Int)
        d = dim mp        
        
        se' | wgon == WgOnTrs = RS.BigAnd $ se : [  RS.SelectTrs r | r <- Trs.rules strs]
            | otherwise = se

        se = RS.rsSelect rs prob 
          
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


weightgapProcessor :: T.Transformation WeightGap P.AnyProcessor
weightgapProcessor = T.Transformation WeightGap

-- | This processor implements the weightgap principle.   
weightgap :: T.TheTransformer WeightGap
weightgap =  T.Transformation WeightGap `T.withArgs` (WgOnAny :+: RS.selAnyOf RS.selStricts :+: Algebraic :+: Nothing :+: nat 2 :+: nat 2 :+: Nothing :+: Just (nat 3) :+: True :+: False)


wgOn :: T.TheTransformer WeightGap -> WgOn -> T.TheTransformer WeightGap
wg `wgOn` on = T.modifyArguments f wg
  where f (_ :+: as) =  on :+: as

