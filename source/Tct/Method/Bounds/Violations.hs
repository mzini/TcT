{-# LANGUAGE BangPatterns #-}

----------------------------------------------------------------------------------
-- |
-- Module      :  Tct.Method.Bounds.Violations
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- License     :  LGPL (see COPYING)
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
--
-- This module implements constructs automata compatible with enriched systems,
-- as employed in the bound processor.
----------------------------------------------------------------------------------

module Tct.Method.Bounds.Violations where

import qualified Data.Set as Set
import Control.Monad (liftM, foldM)

import qualified Termlib.Rule as R
import Termlib.Trs (Trs)
import Termlib.Rule (Strictness(..))
import qualified Termlib.Trs as Trs

import Tct.Processor (SolverM)
import Tct.Method.Bounds.Automata
import Tct.Method.Bounds.Violations.Find
import Tct.Method.Bounds.Violations.Fix

makeRuleCompatible :: R.Rule -> Enrichment -> Strictness -> WeakBoundedness -> Label -> Automaton -> Either Automaton Automaton
makeRuleCompatible r !e !str !wb !ml !a = case null violations of
                                       True  -> Right a
                                       False -> Left $ foldl fixViolation a violations
    where violations = Set.toList $ findViolations a e str wb ml r

compatibleAutomaton :: SolverM m => Trs -> Trs -> Enrichment -> Automaton -> m Automaton
compatibleAutomaton strict weak e a = eitherVal `liftM` (iter a (1 :: Int))
    where iter a' i = do r' <- foldM (f i WeakRule $ maxlabel a') (Right a') wrs
                         r <- foldM (f i StrictRule $ maxlabel a') r' srs
                         case r of
                           Left  a'' -> iter a'' (i + 1)
                           Right a'' -> return $ Right a''
          f _ str ml a' rule = case a' of 
                                (Left a'')  -> return $ Left $ eitherVal $ makeRuleCompatible rule e str wb ml a''
                                (Right a'') -> return $ makeRuleCompatible rule e str wb ml a''
              -- where tl v = do debugMsg $ show $ (brackets $ text $ show i) <+> text "processing rule" <+> pprint rule $$ pprint (eitherVal v)
              -- return v

          eitherVal (Left v)  = v
          eitherVal (Right v) = v
          srs = Trs.rules strict
          wrs = Trs.rules weak
          wb = if Trs.isCollapsing strict then WeakMayExceedBound else WeakMayNotExceedBound
