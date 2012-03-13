{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveDataTypeable #-}

{- | 
Module      :  Tct.Method.InnermostRuleRemoval
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

This module implements the /innermost rule removal/ transformation.
-}

module Tct.Method.InnermostRuleRemoval
    ( irr
      -- * Proof Object
    , IRRProof (..)
    , RuleRemoval (..)
      -- * Processor
    , irrProcessor
    , InnermostRuleRemoval
    ) 
where

import Data.Maybe (isJust, catMaybes)
import Text.PrettyPrint.HughesPJ hiding (empty)

import Tct.Utils.Enum (enumeration')
import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor.Args as A
import Termlib.Problem hiding (Strategy, variables, strategy)
import Termlib.Rule (Rule, rewrite)
import Termlib.Term (immediateSubterms)
import Termlib.Trs ((\\), RuleList(..), unions, fromRules)
import Termlib.Utils (PrettyPrintable(..), paragraph)

import qualified Termlib.Problem as Prob
import qualified Termlib.Rule as R

data InnermostRuleRemoval = InnermostRuleRemoval deriving (Show)

data RuleRemoval = RuleRemoval { removed :: [Rule], reason :: Rule}
      
data IRRProof = IRRProof { inputProblem :: Problem
                         , removals     :: [RuleRemoval]
                         }
              | NotApplicable String

instance PrettyPrintable IRRProof where 
    pprint (NotApplicable r) = paragraph "The processor is not applicable, reason is:" $+$ (nest 1 $ text r)
    pprint proof | length (removals proof) == 0 = paragraph "The input problem contains no overlaps that give rise to inapplicable rules."
                 | otherwise                   = paragraph "Arguments of following rules are not normal-forms:" 
                                                 $+$ text ""
                                                 $+$ pprint (trs, Prob.signature prob, Prob.variables prob)
                                                 $+$ text ""
                                                 $+$ paragraph "All above mentioned rules can be savely removed."
                 where trs  = unions [ fromRules (removed rr) | rr <- removals proof] 
                       prob = inputProblem proof


instance T.TransformationProof InnermostRuleRemoval where 
    answer proof = case (T.transformationProof proof, T.subProofs proof) of 
                     (NotApplicable _, _             ) -> P.MaybeAnswer
                     (IRRProof _ _   , [(_,subproof)]) -> P.answer subproof
                     (IRRProof _ _   , _             ) -> P.MaybeAnswer
    pprintTProof _ _ = pprint
              
instance T.Transformer InnermostRuleRemoval where
    type T.ArgumentsOf InnermostRuleRemoval = A.Unit
    type T.ProofOf     InnermostRuleRemoval = IRRProof
    name        InnermostRuleRemoval = "irr"
    arguments   InnermostRuleRemoval = Unit
    description InnermostRuleRemoval = [ "This processor removes rules 'f(l_1,...,l_n) -> r' for which l_i (1 <= i <=n) is not a normal form."
                                       , "The processor applies only to innermost problems." ]
    transform _ prob = 
        return $ case (Prob.strategy prob, null allRemovals) of 
                   (Innermost, True ) -> T.NoProgress proof
                   (Innermost, False) -> T.Progress proof (enumeration' [(\ trs -> trs \\ rs) `mapRules` prob]) 
                                            where rs = Trs $ concatMap removed allRemovals
                   _                  -> T.NoProgress $ NotApplicable "Input problem is not restricted to innermost rewriting"
        where Trs innerRules  = Prob.trsComponents prob
              Trs allRules    = Prob.allComponents prob
              allRemovals = catMaybes $ mkRemoval `map` innerRules
              mkRemoval cause = case [r | r <- allRules, removable cause r] of 
                                 []   -> Nothing
                                 rems -> Just $ RuleRemoval rems cause
              removable reas rule = any (\ li -> isJust $ rewrite li reas) $ immediateSubterms $ R.lhs rule
              proof = IRRProof { inputProblem = prob
                               , removals     = allRemovals }


irrProcessor :: T.Transformation InnermostRuleRemoval P.AnyProcessor
irrProcessor = T.Transformation InnermostRuleRemoval

-- | On innermost problems, this processor removes inapplicable rules by looking at non-root overlaps.
irr :: T.TheTransformer InnermostRuleRemoval
irr = irrProcessor `T.withArgs` ()
