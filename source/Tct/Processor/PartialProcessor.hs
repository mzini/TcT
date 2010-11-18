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

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Tct.Processor.PartialProcessor where

import Control.Monad (liftM)
import Text.PrettyPrint.HughesPJ

import Termlib.Problem
import Termlib.Trs (Trs)
import Termlib.Utils (PrettyPrintable(..), paragraph)
import qualified Termlib.Trs as Trs

import Tct.Certificate
import Tct.Processor.Args
import Tct.Processor.PPrint (enumeration')
import Tct.Proof
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import qualified Tct.Processor.Transformations as T

data PartialProc p = PartialProc p

data PartialProof p = PartialProof { inputProblem :: Problem
                                   , ppProof :: S.ProofOf p
                                   , ppStrict :: Trs
                                   }

instance S.Processor p => Answerable (PartialProof p) where
  answer = answer . ppProof

instance S.Processor p => PrettyPrintable (PartialProof p) where
  pprint p = text "The following rules were strictly oriented by the relative processor:"
              $+$ pprint (ppStrict p, signature $ inputProblem p, variables $ inputProblem p)
              $+$ pprint (ppProof p)

class S.Processor p => PartialProcessor p where
  solvePartial :: P.SolverM m => S.TheProcessor p -> Problem -> m (PartialProof p)

instance PartialProcessor p => T.Transformer (PartialProc p) where
  name (PartialProc p) = S.name p
  type T.ArgumentsOf (PartialProc p) = S.ArgumentsOf p
  type T.ProofOf (PartialProc p) = PartialProof p
  arguments (PartialProc p) = S.arguments p
  transform inst prob = do res <- solvePartial (S.TheProcessor p args) prob
                           case succeeded res of
                             False -> return $ T.Failure res
                             True  -> case relation prob of
                                        Standard trs         -> return $ T.Success res $ enumeration' [prob'{relation = Standard $ trs Trs.\\ ppStrict res}]
                                        Relative strict weak -> return $ T.Success res $ enumeration' [prob'{relation = Relative (strict Trs.\\ ppStrict res) weak}]
                                        DP       _      _    -> error "Relative Rule Removal inapplicable for DP problems"
    where (PartialProc p) = T.transformation inst
          args            = T.transformationArgs inst
          prob'           = prob{startTerms = TermAlgebra}

-- applyPartial :: (P.SolverM m, PartialProcessor proc, Arguments (S.ArgumentsOf proc)) => proc -> Domains (S.ArgumentsOf proc) -> Problem -> m (P.Proof (PartialProc proc))
-- applyPartial proc args prob = solvePartial (S.TheProcessor proc args) prob >>= mkProof
--     where inst = PartialProc $ proc `S.withArgs` args
--           mkProof = return . P.Proof inst prob

data ChoiceProc p sub = ChoiceProc p

data EitherProof p q = LeftProof p | RightProof q

instance (PrettyPrintable p, PrettyPrintable sub) => PrettyPrintable (EitherProof p sub) where
  pprint (LeftProof p)  = pprint p
  pprint (RightProof q) = pprint q

instance (Answerable p, Answerable sub) => Answerable (EitherProof p sub) where
  answer (LeftProof p)  = answer p
  answer (RightProof q) = answer q

instance (ParsableArguments (S.ArgumentsOf p), PartialProcessor p, P.Processor sub) => S.Processor (ChoiceProc p sub) where
  type S.ArgumentsOf (ChoiceProc p sub) = Arg Bool :+: S.ArgumentsOf p :+: Arg (Maybe (S.StdProcessor sub))
  type S.ProofOf (ChoiceProc p sub) = EitherProof (S.ProofOf p) (T.TProof (PartialProc p) sub)
  name (ChoiceProc p) = S.name p
  description (ChoiceProc p) = S.description p
  arguments (ChoiceProc p) = opt { name = "strict"
                                      , description = unlines [ "If this flag is set and the processor fails to remove any strict rules,"
                                                              , "this processor aborts. Otherwise, it still applies the subprocessor."]
                                      , defaultValue = True }
                             :+: S.arguments p
                             :+: opt { name = "XXX"
                                     , description = unlines [ "The subprocessor that is applied after the current processor."
                                                             , "The value 'none' forces the current processor to orient all rules strictly."]
                                     , defaultValue = Nothing }
  solve inst prob = case sub of
                      Nothing   -> LeftProof `liftM` S.solve (S.TheProcessor p args) prob
                      Just sub' -> do let trans = T.calledWith (PartialProc p) args strict True sub'
                                      res <- P.solve trans prob
                                      return $ RightProof res
    where (ChoiceProc p)          = S.processor inst
          strict :+: args :+: sub = S.processorArgs inst

instance (PartialProcessor p, P.Processor sub) => PrettyPrintable (T.TProof (PartialProc p) sub) where
  pprint (T.UTProof _ sub)  = paragraph (unlines [ "This processor is not applicable for DP Problems."
                                                 , " We continue with the subprocessor." ])
                              $+$ pprint sub
  pprint (T.TProof  p subs) = case succeeded p of
                                True  -> text "First we apply the relative processor:"
                                         $+$ pprint p
                                         $+$ text "Next, we apply the subprocessor:"
                                         $+$ case sub of
                                               Nothing   -> text "No subproof given."
                                               Just sub' -> pprint sub'
                                False -> text "The relative processor was not successful:"
                                         $+$ pprint p
    where sub = if length subs == 1 then snd (head subs) else error "Tct.Processor.PartialProcessor.TProof.pprint: number of subproofs not equal to 1."

instance (PartialProcessor p, P.Processor sub) => Answerable (T.TProof (PartialProc p) sub) where
  answer = T.answerTProof ans
    where ans (PartialProof prob p trs) subs = answerFromCertificate $ certified (unknown, res)
            where res = case relation prob of
                          Standard strict      -> (op strict) (upperBound $ certificate p) subBound
                          Relative strict weak -> if Trs.isNonSizeIncreasing weak then (op strict) (upperBound $ certificate p) subBound else unknown
                          DP       _      _    -> unknown
                  subBound = maximum $ (poly $ Just 0) : map (upperBound . certificate . snd) subs
                  op strict = if Trs.isNonSizeIncreasing (strict Trs.\\ trs) then op' else iter'
                  op' = if Trs.isNonSizeIncreasing trs then mult else compose'
                  compose' r s = r `mult` (s `compose` (poly (Just 1) `add` r))
                  iter' r s = r `mult` (s `iter` r)
