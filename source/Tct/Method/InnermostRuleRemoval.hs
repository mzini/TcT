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

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Tct.Method.InnermostRuleRemoval
    ( irr
    , irrProcessor
    , InnermostRuleRemoval
    , IRRProof (..)
    ) 
where

import Data.Maybe (isJust, catMaybes)
import Data.Typeable
import Text.PrettyPrint.HughesPJ hiding (empty)

import Tct.Processor.PPrint (enumeration')
import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor.Args as A
import Termlib.Problem hiding (Strategy, variables, strategy)
import Termlib.Rule (Rule, rewrite)
import Termlib.Term (immediateSubterms)
import Termlib.Trs ((\\), Trs(..))
import Termlib.Utils (PrettyPrintable(..))

import qualified Termlib.Problem as Prob
import qualified Termlib.Rule as R

data InnermostRuleRemoval = InnermostRuleRemoval deriving (Show,Typeable)

data RuleRemoval = RuleRemoval { removed :: [Rule], reason :: Rule}
      
data IRRProof = IRRProof { inputProblem :: Problem
                         , removals     :: [RuleRemoval]
                         }
              | NotApplicable String

instance PrettyPrintable IRRProof where 
    pprint (NotApplicable r)            = text "The processor is not applicable, reason is:" $$ (nest 1 $ text r)
    pprint proof | length (removals proof) == 0 = text "The input problem contains no overlaps that give rise to inapplicable rules."
                 | otherwise                   = text "Following rules were removed:"
                                                 $+$ (nest 3 $ hcat $ map pprr $ removals proof)
             where pprr rr = text "The rule" <+> ppr (reason rr) 
                             $+$ text "makes following rules inapplicable:"
                             $+$ (nest 3 $ (hcat $ map ppr (removed rr)))
                             $+$ text ""
                             $+$ text ""
                   ppr r   = pprint (r, sig, vars)
                   sig     = Prob.signature $ inputProblem proof
                   vars    = Prob.variables $ inputProblem proof


instance T.TransformationProof IRRProof where 
    answer _ (NotApplicable _)   _         = P.MaybeAnswer
    answer _ (IRRProof _ _)      [(_,p)]   = P.answer p
    answer _ (IRRProof _ _)      ps        = error $ show msg 
      where msg = text ("Tct.Method.InnermostRuleRemoval: Expecting 1 subproof but received " ++ show (length ps))
              
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


irrProcessor :: T.TransformationProcessor InnermostRuleRemoval P.AnyProcessor
irrProcessor = T.transformationProcessor InnermostRuleRemoval


-- irr :: P.Processor sub => P.InstanceOf sub -> P.InstanceOf (T.TransformationProcessor InnermostRuleRemoval sub)
irr :: T.TheTransformer InnermostRuleRemoval
irr = InnermostRuleRemoval `T.calledWith` ()
