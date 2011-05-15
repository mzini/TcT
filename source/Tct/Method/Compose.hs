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

{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Tct.Method.Compose where

import Data.Typeable (Typeable)
import Data.Either (partitionEithers)
import Data.List (intersperse)
import Text.PrettyPrint.HughesPJ

import qualified Tct.Processor as P
import qualified Tct.Processor.Transformations as T
import Tct.Processor.Args
import qualified Tct.Processor.Args as A
import Tct.Processor.PPrint
import Tct.Processor.Args.Instances
import Tct.Processor (Answerable (..), ComplexityProof, certificate)
import qualified Tct.Certificate as Cert

import Termlib.Trs.PrettyPrint (pprintNamedTrs)
import Termlib.Utils (PrettyPrintable (..), paragraph)
import Termlib.Trs (Trs(..), union, (\\))
import qualified Termlib.Trs as Trs
import qualified Termlib.Rule as Rule
import Termlib.Problem (Problem (..), StartTerms (..))
import qualified Termlib.Problem as Prob
import Termlib.Trs.PrettyPrint (pprintNamedTrs)
-- static partitioning


data Partitioning = Random | SeparateDP | Dynamic deriving (Bounded, Ord, Eq, Show, Typeable, Enum) 
data ComposeBound = Add | Mult | Compose  deriving (Bounded, Ord, Eq, Show, Typeable, Enum) 

-- Processor

data ComposeProc p = ComposeProc

data ComposeProof p = ComposeProof ComposeBound (Maybe String) ComposeBound Partitioning (Either (P.Proof p) (P.PartialProof (P.ProofOf p)))

appliedCompose :: ComposeProof p -> ComposeBound
appliedCompose (ComposeProof _ _ compfn _ _) = compfn

instance (P.Processor p) => T.Transformer (ComposeProc p) where
    type T.ArgumentsOf (ComposeProc p) = Arg (EnumOf Partitioning) :+: Arg (EnumOf ComposeBound) :+: Arg (Proc p)
    type T.ProofOf (ComposeProc p)     = ComposeProof p

    name ComposeProc        = "compose"
    -- instanceName inst   = show $ (text $ T.name $ T.transformation inst) <+> parens ppsplit
    --     where split :+: _ :+: _ = T.transformationArgs inst
    --           ppsplit = case msplit of 
    --                       Just split -> text "split with function" <+> text (show split)
    --                       Nothing    -> text "split according to first processor"

    description ComposeProc = [ unwords [ -- "Given a TRS R, 'compose p1 p2' partitions R into a pair of TRSs (R_1,R_2)" 
                                    -- , "and applies processor 'p1' on the (relative) problem R_1 modulo R_2."
                                    -- , "Depending on the flag 'relative' the second processor 'p2' is either applied"
                                    -- , "on the relative problem R_2 modulo R_1 or the TRS R_2."
                                    -- , "In the former case the asymptotic upper-bound for the complexity of R is the worst upper-bound of R_1 modulo R_2 and R_2 modulo R_1.\n"
                                    -- , "In the latter case the complexity of R is computed based on the complexity"
                                    -- , "of R_1 modulo R_2 and the TRS R_2 as follows.\n"
                                    -- , "  1) if R_1 and R_2 are non-size-increasing then dc(n, ->_R) = O(dc(n, ->_R_1/R_2) * dc(n, ->_R_2))\n"
                                    -- , "  2) if R_2 is non-size-increasing then dc(n, ->_R) = O(dc(n, ->_R/S) * dc(n + dc(n,->_R_1/R_2), ->_R_2))\n"
                                    -- , "  3) otherwise dc(n, ->_R) = O(dc(n, ->_R/S) * f(n)) where f(n) denotes m-times iteration of the function \\n. dc(n,->_R_2) where m :=  dc(n,->_R_1/R_2) + 1.\n\n"
                                    -- , "Note that criteria 1--3 are only applied for derivational complexity analysis.\n\n"
                                    -- , "The processor is also applicable in the dependency pair setting and on relative input problems (without criteria 1--3)."
                                    ]
                          ]
    arguments ComposeProc   = opt { A.name         = "split" 
                                  , A.defaultValue = Dynamic
                                  , A.description  = unwords [
                                                 -- "If this argument is set then the input TRS R is partitioned into TRSs (R_1,R_2) according to the supplied argument."
                                                 --        , "If 'Random' is supplied, the strict TRSs R are splitted equally in size."
                                                 --        , "If 'SplitDP' is supplied, the first processor processes is applied to the subproblem where DPs are strict and the remaining strict rules are weak,"
                                                 --        , "and the second processor is applied to the inverse problem."
                                                        ]}
                          :+: opt { A.name = "allow"
                                  , A.defaultValue = Add
                                  , A.description = unwords [ 
                                                    --  "This flag specifies how the second component R_2 is handled by the second given processor 'p2'."
                                                    -- , "If this flag is set, and one of the above criteria 1--3 applies, processor 'p2' is used to estimate the complexity of R_2."
                                                    -- , "Otherwise, the processor 'p2' is applied on the subproblem R_2 modulo R_1."
                                                    ] }
                          :+: arg { A.name = "subprocessor"
                                  , A.description = unlines []}

    transform inst prob = 
        case split of 
          Dynamic -> do sp1 <- P.solvePartial inst1 sizeIncStricts prob
                        let rTrs = Trs.fromRules (P.ppRemovableTrs sp1)
                            sTrs = Prob.strictTrs prob \\ rTrs
                            rDPs = Trs.fromRules (P.ppRemovableDPs sp1)
                            sDPs = Prob.strictDPs prob \\ rDPs
                        return $ mkResult (Right sp1) (rDPs, sDPs) (rTrs, sTrs)
          SeparateDP -> do sp1 <- P.apply inst1 prob1
                           return $ mkResult (Left sp1) (Trs.empty, Prob.strictDPs prob) (Prob.strictTrs prob, Trs.empty)
              where prob1 = prob { strictDPs = Trs.empty
                                 , weakDPs   = Prob.dpComponents prob}
          Random -> do sp1 <- P.apply inst1 prob1
                       return $ mkResult (Left sp1) (rDPs, sDPs) (rTrs, sTrs)
              where (rDPs, sDPs) = halve $ Prob.strictDPs prob
                    (rTrs, sTrs) = halve $ Prob.strictTrs prob
                    prob1 = prob { strictDPs = rDPs
                                 , strictTrs = rTrs
                                 , weakDPs   = sDPs `Trs.union` weakDPs prob
                                 , weakTrs   = sTrs `Trs.union` weakTrs prob}
                    halve (Trs rs) = (Trs rs1,Trs rs2)
                        where (rs1, rs2) = partitionEithers [ if b then Left rule else Right rule 
                                                              | (b,rule) <- zip (intersperse True (repeat False)) rs]

        where split :+: compfn :+: inst1 = T.transformationArgs inst
              sizeIncStricts  = filter Rule.isSizeIncreasing (Trs.rules $ Prob.strictComponents prob)
              weaks   = Prob.weakComponents prob

              mkResult esp1 (rDPs, sDPs) (rTrs, sTrs)
                  | progress esp1 = T.Progress tproof  (enumeration'  [prob2])
                  | otherwise     = T.NoProgress tproof
                  where tproof = ComposeProof compfn mreason employedCompfn split esp1
                        progress (Left sp1)  = not (Trs.isEmpty rDPs && Trs.isEmpty rTrs) && P.succeeded sp1
                        progress (Right sp1) = null (P.ppRemovableTrs sp1) && null (P.ppRemovableDPs sp1)
                        prob2 | employedCompfn == Add = prob { strictTrs  = sTrs
                                                            , strictDPs  = sDPs
                                                            , weakTrs    = rTrs `union` Prob.weakTrs prob
                                                            , weakDPs    = rDPs `union` Prob.weakDPs prob }
                              | otherwise            = prob { startTerms = TermAlgebra
                                                            , strictTrs  = sTrs
                                                            , strictDPs  = sDPs }
                        (mreason, employedCompfn)
                            | Trs.isSizeIncreasing weaks = (Just "some weak rule is size increasing", Add)
                            | otherwise = case compfn of 
                                            Add                                 -> (Nothing, Add)
                                            Mult    | null sizeIncStricts       -> (Nothing, Mult)
                                                    | otherwise                 -> (Just "some strict rule is size increasing", Add)
                                            Compose | Trs.isSizeIncreasing sDPs -> (Just "some strict DP is size increasing", Add)
                                                    | Trs.isSizeIncreasing sTrs -> (Just "strict Trs is size increasing", Add)
                                                    | otherwise                 -> (Nothing, Compose)

                                  


instance P.Processor p => T.TransformationProof (ComposeProc p) where
    answer proof = case (T.transformationProof proof, T.subProofs proof)  of 
                     (tproof@(ComposeProof _ _ _ _ esp1), [(_,sp2)]) -> mkAnswer (appliedCompose tproof) esp1 sp2
                     _                                               -> P.MaybeAnswer
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
                        ubound :: P.Answerable p => p -> Cert.Complexity
                        ubound p = Cert.upperBound $ certificate $ answer p
    pprintProof t prob (tproof@(ComposeProof compfn mreason _ split esp1)) =
        (text "We use the processor" <+> tName <+> text "to orient following rules strictly."
         <+> parens ppsplit)
        $+$ text ""
        $+$ pptrs "Dependency Pairs" rDPs
        $+$ pptrs "TRS Component" rTrs
        $+$ text ""
        $+$ text "The induced complexity of" <+> tName <+> text "on above rules is" <+> pprint (either P.answer P.answer esp1) <> text "."
        $+$ block' "Subproof" [pprint subproof] 
        $+$ (case mreason of 
               Just r  -> text "Since" <+> text r <+> text "we have to move above rules to the corresponding weak components."
                         <+> parens (text "Despite flag" <+> qtext (show compfn) <+> text "was specified.")
               Nothing -> text "We remove the above rules from the input problem."
             <+> text "The overall complexity is obtained by" 
             <+> qtext (case appliedCompose tproof of 
                          Add     -> "addition"
                          Mult    -> "multiplication"
                          Compose -> "composition") <> text ".")

            where rDPs = either (Prob.strictDPs . P.inputProblem) (Trs . P.ppRemovableDPs) esp1
                  rTrs = either (Prob.strictTrs . P.inputProblem) (Trs . P.ppRemovableTrs) esp1
                  sig = Prob.signature prob
                  vars = Prob.variables prob
                  subproof = either P.result P.ppResult esp1
                  qtext = quotes . text
                  tName = qtext $ T.instanceName t
                  pptrs = pprintNamedTrs sig vars
                  ppsplit = text $ case split of 
                                     Random     -> "These rules were chosen randomly"
                                     SeparateDP -> "These rules exclude all dependency pairs"
                                     Dynamic    -> "These rules where chosen dynamically"

                                          -- instance (P.Processor p1, ComplexityProof (P.ProofOf p1) 
--          , P.Processor p2, ComplexityProof (P.ProofOf p2))
--     => PrettyPrintable (ComposeProof p1 p2) where
--     pprint RelativeEmpty = paragraph "The strict component is empty."
--     pprint (NoRuleRemoved p) = pprint p
--     pprint (StaticPartitioned split proof1 proof2) = 
--         text "We decompose the input using the function" <+> quotes (pprint split)
--         $+$ text ""
--         $+$ pprint proof1
--         $+$ text ""
--         $+$ pprint proof2
--     pprint (DynamicPartitioned relApplied prel subproof) = 
--         pprint prel
--         $+$ text ""
--         $+$ paragraph (unlines [ if relApplied then "Above strictly oriented rules were removed." else "Above strict rules are moved into the weak component." 
--                                , "The proof for the resulting subproblem looks as follows."])
--         $+$ text ""
--         $+$ pprint subproof




composeProcessor :: T.TransformationProcessor (ComposeProc P.AnyProcessor) P.AnyProcessor
composeProcessor = T.transformationProcessor ComposeProc

compose :: (P.Processor p1) => Partitioning -> ComposeBound -> P.InstanceOf p1 -> T.TheTransformer (ComposeProc p1)
compose split compfn sub = ComposeProc `T.calledWith` (split :+: compfn :+: sub)


composeDP :: (P.Processor p1) => ComposeBound -> P.InstanceOf p1 -> T.TheTransformer (ComposeProc p1)
composeDP = compose SeparateDP

composeRandom :: (P.Processor p1) => ComposeBound -> P.InstanceOf p1 -> T.TheTransformer (ComposeProc p1)
composeRandom = compose Random

composeDynamic :: (P.Processor p1) => ComposeBound -> P.InstanceOf p1 -> T.TheTransformer (ComposeProc p1)
composeDynamic = compose Dynamic

-- composeStatic :: (P.Processor p1, P.Processor p2) => PartitionFn -> Bool -> P.InstanceOf p1 -> P.InstanceOf p2 -> P.InstanceOf (S.StdProcessor (ComposeProc p1 p2))
-- composeStatic split relative p1 p2 = S.StdProcessor ComposeProc `S.withArgs` (Just split :+: relative :+: p1 :+: p2)