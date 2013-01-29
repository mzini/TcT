{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}

{- | 
Module      :  Tct.Method.Bounds
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>,
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

This module implements the bounds processor.
-}

module Tct.Method.Bounds 
 ( bounds
 , InitialAutomaton (..)
 , Enrichment (..)
   -- * Processor
 , Bounds
 , boundsProcessor
   -- * Proof Object
 , BoundsProof (..)
 , BoundsCertificate (..)
 )
where

import Data.Typeable
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ hiding (empty)

import Termlib.Problem (StartTerms(..), strictComponents, weakComponents)
import qualified Termlib.Problem as Prob
import Termlib.Utils
import Termlib.Trs (Trs)
import qualified Termlib.Trs as Trs
import Termlib.FunctionSymbol (Signature)
import qualified Termlib.FunctionSymbol as FS

import Tct.Certificate (certified, unknown, poly)
import Tct.Processor (ComplexityProof(..), Answer(..))
import qualified Tct.Processor.Standard as S
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances
import Tct.Processor.Args
import Tct.Method.Bounds.Automata
import Tct.Method.Bounds.Violations

-- | This datatype represents the initial automaton
-- employed.
data InitialAutomaton = Minimal -- ^ Employ a minimal set of states,
                                -- separating constructors from defined symbols
                                -- in the case of runtime complexity analysis.
                      | PerSymbol -- ^ Employ a state per function symbol.
                                  -- Slower, but more precise compared to 'Minimal'.
  deriving (Typeable, Enum, Bounded, Eq)

instance Show InitialAutomaton where 
    show Minimal          = "minimal"
    show PerSymbol        = "perSymbol"

data Bounds = Bounds deriving (Typeable) 

-- proof object

data BoundsCertificate = BoundsCertificate { boundHeight    :: Int
                                           , automaton      :: Automaton
                                           , sig            :: Signature }

data BoundsProof = BP Enrichment (Maybe BoundsCertificate)

instance ComplexityProof BoundsProof where
    pprintProof (BP e Nothing) _ = paragraph (show e ++ "-boundness of the problem could not be verified.") 
    pprintProof (BP e (Just p)) _ = paragraph ("The problem is " ++ show e ++ "-bounded by " ++ show (boundHeight p) ++ "."
                                               ++ " The enriched problem is compatible with the following automaton.")
                                    $+$ pprint (toRules (automaton p), (sig p))
    answer (BP _ Nothing) = MaybeAnswer
    answer (BP _ _)       = CertAnswer $ certified (unknown, poly (Just 1))

-- processor
instance S.Processor Bounds where
    name Bounds = "bounds"
    description Bounds = [ unwords [ "This processor implements the (match|roof|top)-bounds technique"
                                   , "that induces linear derivational- and runtime-complexity for right-linear problems." 
                                   , "For non-right-linear problems this processor fails immediately."] ]

    type ArgumentsOf Bounds = Arg (EnumOf InitialAutomaton) :+: Arg (EnumOf Enrichment)

    instanceName inst = "Bounds with " ++ show e ++ "-enrichment and initial automaton '" ++ show i ++ "'"
        where e :+: i = S.processorArgs inst

    arguments Bounds = opt { A.name         = "initial"
                           , A.description  = unwords ["The employed initial automaton."
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

    type ProofOf Bounds     = BoundsProof

    solve inst prob | isApplicable = do a <- compatibleAutomaton strict weak e i
                                        return $ BP e (Just $ BoundsCertificate (maximum $ 0 : [l | (_, l) <- Set.toList $ symbols a]) a sign)
                    | otherwise    = return $ BP e Nothing
        where strict       = strictComponents prob
              weak         = weakComponents prob
              sign         = Prob.signature prob
              st           = Prob.startTerms prob
              isApplicable = Trs.isRightLinear $ strict `Trs.union` weak
              i' :+: e     = S.processorArgs inst
              -- e | e' == Default = if Trs.isRightLinear (strict `Trs.union` weak) then Match else Roof
              --   | otherwise     = e'
              i = case i' of 
                    PerSymbol -> perSymInitialAutomaton strict weak st sign
                    Minimal   -> minimalInitialAutomaton strict weak st sign

-- | This processor implements the bounds technique.
bounds :: InitialAutomaton -> Enrichment -> S.ProcessorInstance Bounds
bounds initialAutomaton enrichment = S.StdProcessor Bounds `S.withArgs` (initialAutomaton :+: enrichment)

boundsProcessor :: S.StdProcessor Bounds
boundsProcessor = S.StdProcessor Bounds

mkMinRules :: Set.Set FS.Symbol -> Signature -> [State] -> State -> [Rule]
mkMinRules fs sign qs q = [ Collapse (f,0) (take (FS.arity sign f) qs) q | f <- Set.toList $ fs]

minimalInitialAutomaton :: Trs -> Trs -> StartTerms -> Signature -> Automaton
minimalInitialAutomaton strict weak (TermAlgebra fs)   sign = fromRules $ mkMinRules fs' sign (repeat 1) 1 
  where fs' = fs `Set.intersection` Trs.functionSymbols trs
        trs = strict `Trs.union` weak
        
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
perSymInitialAutomaton strict weak (TermAlgebra fs) sign = fromRules $ concatMap (mkPerSymRules sign fs') fs'
  where fs' = Set.toList $ fs `Set.intersection` Trs.functionSymbols trs
        trs = strict `Trs.union` weak
perSymInitialAutomaton strict weak (BasicTerms ds cs) sign = fromRules $ mk ds' ++ mk cs'
  where fs = Trs.functionSymbols trs
        ds' = Set.toList $ fs `Set.intersection` ds
        cs' = Set.toList $ fs `Set.intersection` cs
        trs = strict `Trs.union` weak
        mk roots = concatMap mkBase roots
        mkBase = if null cs' then mkPerSymEmptyRules sign (maximum [ enum f | f <- Set.toList fs ] + 1) else mkPerSymRules sign cs'
