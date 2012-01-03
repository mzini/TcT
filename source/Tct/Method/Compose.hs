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
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Tct.Method.Compose where

import Data.Typeable (Typeable)
import Text.PrettyPrint.HughesPJ
import Data.Typeable ()
import qualified Tct.Processor as P
import qualified Tct.Processor.Transformations as T
import Tct.Processor.Args
import qualified Tct.Processor.Args as A
import Tct.Processor.PPrint
import Tct.Processor.Args.Instances
import Tct.Processor (ComplexityProof (..), certificate)
import qualified Tct.Certificate as Cert

import Termlib.Trs.PrettyPrint (pprintNamedTrs)
import Termlib.Utils (PrettyPrintable (..))
import Termlib.Trs (RuleList(..), union, (\\))
import qualified Termlib.Trs as Trs
import qualified Termlib.Rule as Rule
import Termlib.Problem (Problem (..), StartTerms (..))
import qualified Termlib.Problem as Prob
import Tct.Method.DP.DependencyGraph
import Data.Graph.Inductive.Query.BFS (bfsn)
import qualified Tct.Method.DP.DependencyGraph as DG
-- import Termlib.Term (..)
-- static partitioning

data ComposeBound = Add  -- ^ obtain bound by addition
                  | Mult -- ^ obtain bound by multiplication
                  | Compose  -- ^ obtain bound by composition
  deriving (Bounded, Ord, Eq, Show, Typeable, Enum) 

data RuleSelector a = RS { rsName :: String -- ^ name of the rule selector
                         , rsSelect :: a -> Problem -> Prob.Ruleset -- ^ given state 'a' and problem, select a 'Prob.Ruleset' from the problem
                                                                 -- ^ whose TRSs should be subsets of the TRSs from the input problem.
                         } deriving Typeable

instance Show (RuleSelector a) where show = rsName


selInverse :: RuleSelector a -> RuleSelector a
selInverse s = RS { rsName = "inverse of " ++ rsName s
                  , rsSelect = fn }
    where fn a prob = Prob.Ruleset { Prob.sdp  = inv Prob.strictDPs Prob.sdp
                                   , Prob.wdp  = inv Prob.weakDPs Prob.wdp
                                   , Prob.strs = inv Prob.strictTrs Prob.strs
                                   , Prob.wtrs = inv Prob.weakTrs Prob.wtrs }
              where rs = rsSelect s a prob
                    inv pfn rfn = pfn prob Trs.\\ rfn rs

selCombine :: (String -> String -> String) -> (Trs.Trs -> Trs.Trs -> Trs.Trs) -> (RuleSelector a -> RuleSelector a -> RuleSelector a)
selCombine cn ctrs s1 s2 = RS { rsName = cn (rsName s1) (rsName s2)
                              , rsSelect = fn }
        where fn a prob = Prob.Ruleset { Prob.sdp  = un Prob.sdp
                                       , Prob.wdp  = un Prob.wdp
                                       , Prob.strs = un Prob.strs
                                       , Prob.wtrs = un Prob.wtrs }
                  where rs1 = rsSelect s1 a prob
                        rs2 = rsSelect s2 a prob
                        un rfn = rfn rs1 `ctrs` rfn rs2

selUnion :: RuleSelector a -> RuleSelector a -> RuleSelector a
selUnion = selCombine (\ n1 n2 -> "union of " ++ n1 ++ " and " ++ n2) Trs.union

selInter :: RuleSelector a -> RuleSelector a -> RuleSelector a
selInter= selCombine (\ n1 n2 -> "intersect of " ++ n1 ++ " and " ++ n2) Trs.intersect


selRules :: RuleSelector a
selRules = RS { rsName   = "rewrite-rules" , rsSelect = fn } 
    where fn _ prob = Prob.Ruleset { Prob.sdp = Trs.empty
                                   , Prob.wdp = Trs.empty
                                   , Prob.strs = Prob.strictTrs prob
                                   , Prob.wtrs = Prob.weakTrs prob }
           
selDPs :: RuleSelector a
selDPs = RS { rsName = "DPs" , rsSelect = fn }
    where fn _ prob = Prob.Ruleset { Prob.sdp = Prob.strictDPs prob
                                   , Prob.wdp = Prob.weakDPs prob
                                   , Prob.strs = Trs.empty
                                   , Prob.wtrs = Trs.empty }

selStricts :: RuleSelector a
selStricts = RS { rsName = "strict-rules" , rsSelect = fn }
    where fn _ prob = Prob.Ruleset { Prob.sdp = Prob.strictDPs prob
                                   , Prob.wdp = Trs.empty
                                   , Prob.strs = Prob.strictTrs prob
                                   , Prob.wtrs = Trs.empty }

selFromWDG :: String -> (a -> DG -> Prob.Ruleset) -> RuleSelector a
selFromWDG n f = RS { rsName = n
                    , rsSelect = \a prob -> f a (dg prob) }
    where dg = estimatedDependencyGraph Edg


selFromCWDG :: String -> (a -> CDG -> Prob.Ruleset) -> RuleSelector a
selFromCWDG n f = RS { rsName = n
                     , rsSelect = \a prob -> f a (dg prob) }
    where dg = toCongruenceGraph . estimatedDependencyGraph Edg

restrictToCongruences :: Prob.Ruleset -> [NodeId] -> CDG -> Prob.Ruleset
restrictToCongruences rs ns cdg = rs { Prob.sdp = Trs.fromRules [ r | (DG.StrictDP, r) <- rr]
                                     , Prob.wdp = Trs.fromRules [ r | (DG.WeakDP, r) <- rr] }
    where rr = allRulesFromNodes cdg ns

selFirstCongruence :: RuleSelector a
selFirstCongruence = selFromCWDG "first congruence from CWDG" fn
    where fn _ cdg = restrictToCongruences Prob.emptyRuleset (roots cdg) cdg 

selFirstStrictCongruence :: RuleSelector a
selFirstStrictCongruence = selFromCWDG "first congruence with strict rules from CWDG" fn
    where fn _ cdg = restrictToCongruences Prob.emptyRuleset ns cdg 
              where ns = take 1 $ [ n | n <- bfsn (roots cdg) cdg
                                  , any ((==) DG.StrictDP . fst) (allRulesFromNodes cdg [n])  ]

selBfs :: String -> (CDG -> NodeId -> [NodeId]) -> RuleSelector a
selBfs nm f = selFromCWDG nm fn
    where fn _ dg = restrictToCongruences Prob.emptyRuleset ns dg 
              where ns = concatMap (f dg) (bfsn (roots dg) dg)

                                      


-- splitWithoutLeafs :: RuleSelector a
-- splitWithoutLeafs = Static ("split all rules from CWD except leafs"
--                      , sfc)
--     where sfc _ prob | Trs.isEmpty (Prob.strictDPs prob) = ([],[])
--                      | otherwise = (Trs.rules $ Prob.strictDPs prob Trs.\\ rts, [])
--             where dg = DG.estimatedDependencyGraph Edg prob
--                   cdg = DG.toCongruenceGraph dg
--                   rts = DG.allRulesFromNodes cdg (DG.leafs cdg)

-- splitSatisfying :: String -> (Rule -> Bool) -> RuleSelector a
-- splitSatisfying n p = Static ( n
--                              , const $ \ prob -> ( filter p $ Trs.rules $ Prob.strictDPs prob
--                                                 , filter p $ Trs.rules $ Prob.strictTrs prob))

data Partitioning = Static (RuleSelector ComposeBound) -- ^ Select rules statically according to a 'RuleSelector'
                  | Dynamic  -- ^ Selection of the rules is determined by the applied processor.
 deriving (Typeable)

instance Show Partitioning where
    show Dynamic         = "dynamic"
    show (Static s) = show $ text "statically using" <+> quotes (text (show s))

instance AssocArgument Partitioning where 
    assoc _ = [ ("dynamic",    Dynamic) ] --TODO extend

-- Compose Processor ala Waldmann

data ComposeProc p = ComposeProc

data ComposeProof p = ComposeProof ComposeBound Partitioning [Rule.Rule] (Either (P.Proof p) (P.PartialProof (P.ProofOf p)))
                    | Inapplicable String


progress :: P.Processor p => ComposeProof p -> Bool
progress (ComposeProof _ _ _ esp) = 
  case esp of 
    Left sp1  -> not (Trs.isEmpty $ Prob.strictComponents $ P.inputProblem sp1) && P.succeeded sp1
    Right sp1 -> not (null (P.ppRemovableTrs sp1) && null (P.ppRemovableDPs sp1))
progress Inapplicable {} = False


instance (P.Processor p) => T.Transformer (ComposeProc p) where
    type T.ArgumentsOf (ComposeProc p) = Arg (Assoc Partitioning) :+: Arg (EnumOf ComposeBound) :+: Arg (Proc p)
    type T.ProofOf (ComposeProc p)     = ComposeProof p

    name ComposeProc        = "compose"
    instanceName inst   = show $ text "compose" <+> parens (ppsplit <> text "," <+> ppCompFn)
        where split :+: compFn :+: _ = T.transformationArgs inst
              ppsplit = text $ show split 
              ppCompFn = case compFn of 
                           Add  -> text "addition"
                           Mult -> text "multiplication"
                           Compose -> text "composition"

    description ComposeProc = [ unwords [ "This transformation implements techniques for splitting the complexity problem"
                                        , "into two complexity problems (A) and (B) so that the complexity of the input problem" 
                                        , "can be estimated by the complexity of the transformed problem."
                                        , "The processor closely follows the ideas presented in"
                                        , "/Complexity Bounds From Relative Termination Proofs/"
                                        , "(<http://www.imn.htwk-leipzig.de/~waldmann/talk/06/rpt/rel/main.pdf>)" ]
                              ]
    arguments ComposeProc   = opt { A.name         = "split" 
                                  , A.defaultValue = Dynamic
                                  , A.description  = unwords [ "This argument of type 'Compose.Partitioning' determines strict rules of"
                                                             , "problem (A). Usually, this should be set to 'Dynamic', in which case"
                                                             , "the given processor determines selection of rules dynamically."
                                                             ]}
                          :+: opt { A.name = "allow"
                                  , A.defaultValue = Add
                                  , A.description = unwords [ "This argument type 'Compose.ComposeBound' determines"
                                                            , "how the complexity certificate should be obtained from subproblems (A) and (B)."
                                                            , "Consequently, this argument also determines the shape of (B)."
                                                            , "The third argument defines a processor that is applied on problem (A)."
                                                            , "If this processor succeeds, the input problem is transformed into (B)."
                                                            , "Note that for compose bound 'Mult' the transformation only succeeds"
                                                            , "if applied to non size-increasing Problems."
                                                            ] }
                          :+: arg { A.name = "subprocessor"
                                  , A.description = unlines [ "The processor applied on subproblem (A)."]}

    transform inst prob = 
        case split of 
          Dynamic   -> do sp1 <- P.solvePartial inst1 (forcedDps ++ forcedTrs)  prob
                          let rTrs = Trs.fromRules (P.ppRemovableTrs sp1)
                              sTrs = Prob.strictTrs prob \\ rTrs
                              rDps = Trs.fromRules (P.ppRemovableDPs sp1)
                              sDps = Prob.strictDPs prob \\ rDps
                          return $ mkResult (Right sp1) (rDps, sDps) (rTrs, sTrs)                         
          Static s -> do sp1 <- P.apply inst1 prob1
                         return $ mkResult (Left sp1) (rDps, sDps) (rTrs, sTrs)                         
              where rs             = rsSelect s compfn prob
                    rDps           = Prob.sdp rs `Trs.union` Trs.fromRules forcedDps
                    rTrs           = Prob.strs rs `Trs.union` Trs.fromRules forcedTrs
                    sTrs           = strictTrs prob Trs.\\ rTrs
                    sDps           = strictDPs prob Trs.\\ rDps
                    prob1 = prob { strictDPs = rDps
                                 , strictTrs = rTrs
                                 , weakTrs   = sTrs `Trs.union` weakTrs prob
                                 , weakDPs   = sDps `Trs.union` weakDPs prob }

        where split :+: compfn :+: inst1 = T.transformationArgs inst

              weaks   = Prob.weakComponents prob

              (forcedDps, forcedTrs) = case compfn of 
                                         Compose -> (fsi Prob.strictDPs, fsi Prob.strictTrs)
                                             where fsi f = [ rule | rule <- Trs.rules (f prob), not (Rule.isNonSizeIncreasing rule)]
                                         _       -> ([],[])

              mkResult esp1 (rDPs, sDPs) (rTrs, sTrs)
                  | progress tproof = T.Progress tproof  (enumeration'  [prob2])
                  | otherwise     = T.NoProgress tproof
                  where tproof = maybe (ComposeProof compfn split (forcedDps ++ forcedTrs) esp1) Inapplicable mreason
                        prob2 | compfn == Add = prob { strictTrs  = sTrs
                                                     , strictDPs  = sDPs
                                                     , weakTrs    = rTrs `union` Prob.weakTrs prob
                                                     , weakDPs    = rDPs `union` Prob.weakDPs prob }
                              | otherwise            = prob { startTerms = TermAlgebra
                                                            , strictTrs  = sTrs
                                                            , strictDPs  = sDPs }
              mreason |  not (Trs.isNonSizeIncreasing weaks)
                        && compfn /= Add = Just "some weak rule is size increasing"
                      | otherwise = case compfn of 
                                     Add              -> Nothing
                                     Mult | sizeinc   -> Just "some strict rule is size increasing"
                                          | otherwise -> Nothing
                                     Compose          -> Nothing
                where sizeinc = not $ Trs.isNonSizeIncreasing $ Prob.strictComponents prob
                                 

instance P.Processor p => T.TransformationProof (ComposeProc p) where
      answer proof = case (T.transformationProof proof, T.subProofs proof)  of 
                     (ComposeProof compfn _ _ esp1, [(_,sp2)]) -> mkAnswer compfn esp1 sp2
                     _                                         -> P.MaybeAnswer
        where mkAnswer compfn esp1 sp2 | success   = P.CertAnswer $ Cert.certified (Cert.constant, ub)
                                       | otherwise = P.MaybeAnswer
                  where success = case (either answer answer esp1, answer sp2) of
                                    (P.CertAnswer _, P.CertAnswer _) -> True
                                    _                                -> False
                        ub = case compfn of 
                               Add     -> ub1 `Cert.add` ub2
                               Mult    -> ub1 `Cert.mult` ub2
                               Compose -> ub1 `Cert.mult` (ub2 `Cert.compose` (Cert.poly (Just 1) `Cert.add` ub1))
                        ub1 = either ubound ubound esp1
                        ub2 = ubound sp2
                        ubound :: P.ComplexityProof p => p -> Cert.Complexity
                        ubound p = Cert.upperBound $ certificate p
      pprintTProof _ _ (Inapplicable reason) = text "Compose is inapplicable since" <+> text reason
      pprintTProof t prob (tproof@(ComposeProof compfn split stricts esp1)) = 
        if progress tproof 
        then fsep [text "We use the processor", tName, text "to orient following rules strictly.", parens ppsplit]
             $+$ text ""
             $+$ pptrs "Dependency Pairs" rDPs
             $+$ pptrs "TRS Component" rTrs
             $+$ text ""
             $+$ fsep [text "The induced complexity of", tName, text "on above rules is", pprint (either P.answer P.answer esp1) <> text "."]
             $+$ text ""
             $+$ block' "Sub-proof" [ppSubproof]
             $+$ text ""
             $+$ (text "The overall complexity is obtained by" 
                  <+> qtext (case compfn of 
                                Add     -> "addition"
                                Mult    -> "multiplication"
                                Compose -> "composition") <> text ".")
        else block' "Sub-proof" [ if null stricts 
                                  then text "We fail to orient any rules."
                                       $+$ text ""
                                       $+$ ppSubproof
                                  else text "We have tried to orient orient following rules strictly:"
                                       $+$ text ""
                                       $+$ pptrs "Strict Rules" (Trs stricts)]
            where rDPs = either (Prob.strictDPs . P.inputProblem) (Trs . P.ppRemovableDPs) esp1
                  rTrs = either (Prob.strictTrs . P.inputProblem) (Trs . P.ppRemovableTrs) esp1
                  sig = Prob.signature prob
                  vars = Prob.variables prob
                  qtext = quotes . text
                  tName = qtext $ T.instanceName t
                  pptrs = pprintNamedTrs sig vars
                  ppSubproof = either (\p -> P.pprintProof p P.ProofOutput) (\p -> P.pprintProof p P.ProofOutput) esp1
                  ppsplit = text "These rules where chosen" <+> text (show split) <> text "."

composeProcessor :: T.Transformation (ComposeProc P.AnyProcessor) P.AnyProcessor
composeProcessor = T.Transformation ComposeProc

compose :: (P.Processor p1) => Partitioning -> ComposeBound -> P.InstanceOf p1 -> T.TheTransformer (ComposeProc p1)
compose split compfn sub = T.Transformation ComposeProc `T.withArgs` (split :+: compfn :+: sub)

composeDynamic :: (P.Processor p1) => ComposeBound -> P.InstanceOf p1 -> T.TheTransformer (ComposeProc p1)
composeDynamic = compose Dynamic

composeStatic :: (P.Processor p1) => (RuleSelector ComposeBound) -> ComposeBound -> P.InstanceOf p1 -> T.TheTransformer (ComposeProc p1)
composeStatic rs = compose (Static rs)

