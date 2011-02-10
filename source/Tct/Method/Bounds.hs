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

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Tct.Method.Bounds 
 ( bounds
 , boundsProcessor
 , InitialAutomaton (..)
 , Enrichment (..))
where

import Data.Typeable
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ hiding (empty)

import Termlib.Problem (StartTerms(..), strictTrs, weakTrs)
import qualified Termlib.Problem as Prob
import Termlib.Utils
import Termlib.Trs (Trs)
import qualified Termlib.Trs as Trs
import Termlib.FunctionSymbol (Signature)
import qualified Termlib.FunctionSymbol as FS

import Tct.Proof
import Tct.Certificate (certified, unknown, poly)
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances
import Tct.Processor.Args
import Tct.Method.Bounds.Automata
import Tct.Method.Bounds.Violations

data InitialAutomaton = Minimal | PerSymbol deriving (Typeable, Enum, Bounded, Eq)

instance Show InitialAutomaton where 
    show Minimal          = "minimal"
    show PerSymbol        = "perSymbol"

data Bounds = Bounds deriving (Typeable) 

-- proof object

data BoundsCertificate = BoundsCertificate { boundHeight    :: Int
                                           , automaton      :: Automaton
                                           , sig            :: Signature }

data BoundsProof = BP Enrichment (Maybe BoundsCertificate)

ppEnrichment :: Enrichment -> Doc
ppEnrichment = text . show

instance PrettyPrintable BoundsProof where
    pprint (BP e Nothing)  = (ppEnrichment e) <> text "-boundness" <+> text "of the problem could not be verified." 
    pprint (BP e (Just p)) = text "The problem is" <+> (ppEnrichment e) <> text "-bounded by" <+> pprint (boundHeight p) <> text "."
                             $+$ text "The enriched problem is compatible with the following automaton:"
                             $+$ pprint (toRules (automaton p), (sig p))

instance Verifiable BoundsProof

instance Answerable BoundsProof where
    answer (BP _ Nothing) = MaybeAnswer
    answer (BP _ _)       = CertAnswer $ certified (unknown, poly (Just 1))

-- processor
instance S.Processor Bounds where
    name Bounds = "bounds"
    description Bounds = [ unlines [ "This processor implements the (match|roof|top)-bounds technique"
                                   , "that induces linear derivational- and runtime-complexity for right-linear problems." 
                                   , "For non-right-linear problems this processor fails immediately."] ]

    type S.ArgumentsOf Bounds = Arg (EnumOf InitialAutomaton) :+: Arg (EnumOf Enrichment)

    instanceName inst = "Bounds with " ++ show e ++ "-enrichment and initial automaton '" ++ show i ++ "'"
        where e :+: i = S.processorArgs inst

    arguments Bounds = opt { A.name         = "initial"
                           , A.description  = unlines ["The employed initial automaton."
                                                      , "If 'perSymbol' is set then the initial automaton admits one dedicated"
                                                      , "state per function symbols."
                                                      , "If 'minimal' is set then the initial automaton admits exactly"
                                                      , "one state for derivational-complexity analysis. For runtime-complexity analysis, "
                                                      , "two states are used in order to distinguish defined symbols from constructors."]
                           , A.defaultValue = Minimal} 
                       :+: 
                       opt { A.name         = "enrichment" 
                           , A.description  = "The employed enrichment." 
                           , A.defaultValue = Match}

    type S.ProofOf Bounds     = BoundsProof

    solve inst prob | isApplicable = do a <- compatibleAutomaton strict weak e i
                                        return $ BP e (Just $ BoundsCertificate (maximum $ 0 : [l | (_, l) <- Set.toList $ symbols a]) a sign)
                    | otherwise    = return $ BP e Nothing
        where strict       = strictTrs prob
              weak         = weakTrs prob
              sign         = Prob.signature prob
              st           = Prob.startTerms prob
              isApplicable = Trs.isRightLinear $ strict `Trs.union` weak
              i' :+: e     = S.processorArgs inst
              -- e | e' == Default = if Trs.isRightLinear (strict `Trs.union` weak) then Match else Roof
              --   | otherwise     = e'
              i = case i' of 
                    PerSymbol -> perSymInitialAutomaton strict weak st sign
                    Minimal   -> minimalInitialAutomaton strict weak st sign

bounds :: InitialAutomaton -> Enrichment -> P.InstanceOf (S.StdProcessor Bounds)
bounds initialAutomaton enrichment = Bounds `S.withArgs` (initialAutomaton :+: enrichment)

boundsProcessor :: S.StdProcessor Bounds
boundsProcessor = S.StdProcessor Bounds

mkMinRules :: Set.Set FS.Symbol -> Signature -> [State] -> State -> [Rule]
mkMinRules fs sign qs q = [ Collapse (f,0) (take (FS.arity sign f) qs) q | f <- Set.toList $ fs]

minimalInitialAutomaton :: Trs -> Trs -> StartTerms -> Signature -> Automaton
minimalInitialAutomaton strict weak TermAlgebra        sign = fromRules $ mkMinRules (Trs.functionSymbols $ strict `Trs.union` weak) sign (repeat 1) 1 
minimalInitialAutomaton strict weak (BasicTerms ds cs) sign = fromRules $ mkMinRules ds' sign (repeat 2) 1 ++ mkMinRules cs' sign (repeat 2) 2
    where fs = Trs.functionSymbols trs
          ds' = fs `Set.intersection` ds
          cs' = fs `Set.intersection` cs
          trs = strict `Trs.union` weak

mkPerSymRules :: Signature -> [FS.Symbol] -> FS.Symbol -> [Rule]
mkPerSymRules sign fs f  = [ Collapse (f,0) args (enum f) | args <- listProduct $ take (FS.arity sign f) ffs ]
    where ffs = repeat [enum g | g <- fs]

mkPerSymEmptyRules :: Signature -> State -> FS.Symbol -> [Rule]
mkPerSymEmptyRules sign q f = [Collapse (f,0) (replicate (FS.arity sign f) q) (enum f)]

perSymInitialAutomaton :: Trs -> Trs -> StartTerms -> Signature -> Automaton
perSymInitialAutomaton strict weak TermAlgebra        sign = fromRules $ concatMap (mkPerSymRules sign fs) fs
    where fs = Set.toList $ Trs.functionSymbols trs
          trs = strict `Trs.union` weak
perSymInitialAutomaton strict weak (BasicTerms ds cs) sign = fromRules $ mk ds' ++ mk cs'
    where fs = Trs.functionSymbols trs
          ds' = Set.toList $ fs `Set.intersection` ds
          cs' = Set.toList $ fs `Set.intersection` cs
          trs = strict `Trs.union` weak
          mk roots = concatMap mkBase roots
          mkBase = if null cs' then mkPerSymEmptyRules sign (maximum [ enum f | f <- Set.toList fs ] + 1) else mkPerSymRules sign cs'
