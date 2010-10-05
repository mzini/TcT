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

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}

module Tct.Method.Combinator 
    -- ( bestStrategy
    -- , fastestStrategy
    -- , sequentiallyStrategy
    -- , iteStrategy
    -- , failStrategy
    -- , succStrategy
    -- , best
    -- , fastest
    -- , sequentially
    -- , (.>>)
    -- , ite
    -- , fail
    -- , success
    -- )
where
import Prelude hiding (fail)
import Text.PrettyPrint.HughesPJ hiding (parens)
import Data.List (intersperse)
import Control.Concurrent.PFold (pfoldA, Return (..))
import Text.Parsec.Prim
import Text.Parsec.Char
import Control.Monad (forM)
import Control.Monad.Trans (liftIO)

import Termlib.Utils (PrettyPrintable(..))

import qualified Tct.Processor as P
import Tct.Processor.PPrint
import qualified Tct.Processor.Standard as S
import Tct.Proof
import Tct.Processor.Args
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances ()
import Tct.Processor.Parse

-- failure and success

data TrivialProof = Succeeded 
                  | Failed

instance Answerable TrivialProof where 
    answer Succeeded = YesAnswer
    answer Failed    = NoAnswer

instance PrettyPrintable TrivialProof where 
    pprint Succeeded = text "Success"
    pprint Failed    = text "Fail"

data Fail = Fail deriving (Show)

instance S.StdProcessor Fail where
    type S.ArgumentsOf Fail = NoArgs
    type S.ProofOf Fail     = TrivialProof
    name Fail               = "fail"
    instanceName _          = "fail"
    solve _ _               = return Failed
    description Fail        = ["Processor 'fail' always returns the answer 'No'."]
    arguments Fail          = NoArgs

data Success = Success deriving (Show)

instance S.StdProcessor Success where
    type S.ArgumentsOf Success = NoArgs
    type S.ProofOf Success     = TrivialProof
    name Success               = "success"
    instanceName _             = "success"
    solve _ _                  = return Succeeded
    description Success        = ["Processor 'success' always returns the answer 'Yes'."]
    arguments   Success        = NoArgs

failProcessor :: S.Processor Fail
failProcessor = S.Processor Fail

successProcessor :: S.Processor Success
successProcessor = S.Processor Success

fail :: P.InstanceOf (S.Processor Fail)
fail = Fail `S.calledWith` ()

success :: P.InstanceOf (S.Processor Success)
success = Success `S.calledWith` ()



-- if-then-else

data Ite g t e = Ite

data IteProof g t e = IteProof { guardProof  :: P.ProofOf g
                               , branchProof :: Either (P.ProofOf t) (P.ProofOf e) }

instance ( Answerable (P.ProofOf t)
         , Answerable (P.ProofOf e))
    => Answerable (IteProof g t e) where
      answer p = either answer answer $ branchProof p

instance ( Answerable (P.ProofOf g)
         , PrettyPrintable (P.ProofOf g)
         , PrettyPrintable (P.ProofOf t)
         , PrettyPrintable (P.ProofOf e)) 
    => PrettyPrintable (IteProof g t e) where
        pprint p = ppcond $+$ text "" $+$ ppbranch
            where ppcond   = text ("a) We first check the conditional [" ++ (if suc then "Success" else "Fail") ++ "]:")
                             $+$ (nest 3 $ pprint $ guardProof p)
                  ppbranch = text ("b) We continue with the " ++ (if suc then "then" else "else") ++ "-branch:")
                             $+$ (nest 3 $ either pprint pprint $ branchProof p)
                  suc      = succeeded $ guardProof p

instance ( P.Processor g
         , Answerable (P.ProofOf g)
         , P.Processor t
         , P.Processor e) 
    => P.Processor (Ite g t e) where
        type P.ProofOf (Ite g t e)    = IteProof g t e 
        data P.InstanceOf (Ite g t e) = IteInstance (P.InstanceOf g) (P.InstanceOf t) (P.InstanceOf e)
        name Ite = "if-then-else processor"
        instanceName (IteInstance g _ _) = "Branch on wether processor '" ++ P.instanceName g ++ "' succeeds"
--        fromInstance (IteInstance instg instt inste)  = Ite (P.fromInstance instg) (P.fromInstance instt) (P.fromInstance inste)
        solve_ (IteInstance g t e) prob = do gproof <- P.solve g prob
                                             if succeeded gproof 
                                              then finish gproof Left t
                                              else finish gproof Right e
            where finish gproof d p = do bproof <- P.solve p prob
                                         return $ IteProof { guardProof  = gproof
                                                           , branchProof = d bproof }

instance P.ParsableProcessor (Ite P.AnyProcessor P.AnyProcessor P.AnyProcessor) where
    synopsis        Ite = "if <processor> then <processor> else <processor>"
    parseProcessor_ Ite = do let pb s = try (string s) >> whiteSpace >> P.parseAnyProcessor
                             ginst <- pb "if"
                             whiteSpace
                             tinst <- pb "then"
                             whiteSpace
                             einst <- pb "else"
                             return $ IteInstance ginst tinst einst
    description  _   = ["This processor implements conditional branching."]

ite :: P.InstanceOf g -> P.InstanceOf t -> P.InstanceOf e -> P.InstanceOf (Ite g t e)
ite = IteInstance

iteProcessor :: Ite P.AnyProcessor P.AnyProcessor P.AnyProcessor
iteProcessor = Ite


-- parallel combinators

data OneOf p = Best | Fastest | Sequentially deriving (Eq, Show)

data OneOfProof p = OneOfFailed (OneOf p) [P.Proof p]
                  | OneOfSucceeded (OneOf p) (P.Proof p)

instance Answerable (P.Proof p) => Answerable (OneOfProof p) where
    answer (OneOfFailed _ _)    = MaybeAnswer
    answer (OneOfSucceeded _ p) = answer p

instance (P.ComplexityProcessor p) => PrettyPrintable (OneOfProof p) where
    pprint proof = case proof of 
                     (OneOfFailed _ failures) -> text "None of the processors succeeded."
                                                $+$ text "" 
                                                $+$ detailsFailed (enumeration' failures)
                     (OneOfSucceeded o p)     -> descr o
                                                $+$ text ""
                                                $+$ detailsSuccess (enumeration' [p])
                                                    where descr Sequentially = procName p <+> text "succeeded:"
                                                          descr Fastest      = procName p <+> text "proved the goal fastest:"
                                                          descr Best         = procName p <+> text "proved the best result:"

instance (P.ComplexityProcessor p) => S.StdProcessor (OneOf p) where
    type S.ArgumentsOf (OneOf p) = Arg [S.Processor p]
    type S.ProofOf (OneOf p)     = OneOfProof p

    name Fastest      = "fastest"
    name Sequentially = "sequentially"
    name Best         = "best"

    instanceName inst = c (S.processor inst) ++ " of " ++  (concat $ intersperse ", " [ "'" ++ P.instanceName p ++ "'" | p <- S.processorArgs inst])
        where c Best         = "Best"
              c Fastest      = "Fastest"
              c Sequentially = "Sequentially"

    description Best         = ["Processor 'Best' applies the given list of processors in parallel and returns the proof admitting the lowest complexity certificate."]
    description Fastest      = ["Processor 'Fastest' applies the given list of processors in parallel and returns the first successful proof."]
    description Sequentially = ["Processor 'Sequentially' applies the given list of processors sequentially and returns the first successful proof."]

    arguments _ = arg { A.name        = "subprocessors"
                      , A.description = "a list of subprocessors"}
    solve theproc prob | S.processor theproc == Sequentially = solveSeq (S.processorArgs theproc) []
                       | S.processor theproc == Best         = solveBest (S.processorArgs theproc)
                       | otherwise                           = solveFast (S.processorArgs theproc)

        where mkActions ps = forM ps $ \ proc -> P.mkIO $ P.apply proc prob
              ofResult o (Left faileds) = OneOfFailed o faileds
              ofResult o (Right proof) = OneOfSucceeded o proof
              
              solveSeq []     failures = return $ OneOfFailed Sequentially (reverse failures)
              solveSeq (p:ps) failures = do r <- P.apply p prob
                                            if succeeded r
                                             then return $ OneOfSucceeded Sequentially r
                                             else solveSeq ps (r:failures)
                                
              solveBest = solvePar betterThan final 
                  where p1 `betterThan` p2 = certificate p1 < certificate p2
                        final = const False

              solveFast= solvePar betterThan final
                  where _ `betterThan` _ = True
                        final = const True

              solvePar better final ps = do actions <- mkActions ps
                                            let sel (Left ps') proof | succeeded proof = ret proof
                                                                     | otherwise       = Continue $ Left (proof : ps')
                                                sel (Right p1) p2 | p1 `better` p2 = ret p1
                                                                  | otherwise      = ret p2
                                                ret proof | final proof = Stop $ Right proof
                                                          | otherwise   = Continue $ Right proof
                                            r <- liftIO $ pfoldA sel (Left []) actions
                                            return $ ofResult Best r




bestProcessor :: S.Processor (OneOf P.AnyProcessor)
bestProcessor = S.Processor Best

fastestProcessor :: S.Processor (OneOf P.AnyProcessor)
fastestProcessor = S.Processor Fastest

sequentiallyProcessor :: S.Processor (OneOf P.AnyProcessor)
sequentiallyProcessor = S.Processor Sequentially

best :: (P.ComplexityProcessor p) => [P.InstanceOf p] -> P.InstanceOf (S.Processor (OneOf p))
best ps = Best `S.calledWith` ps

fastest :: (P.ComplexityProcessor p) => [P.InstanceOf p] -> P.InstanceOf (S.Processor (OneOf p))
fastest ps = Fastest `S.calledWith` ps

sequentially :: (P.ComplexityProcessor p) => [P.InstanceOf p] -> P.InstanceOf (S.Processor (OneOf p))
sequentially ps = Sequentially `S.calledWith` ps
