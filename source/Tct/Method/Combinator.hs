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
import Control.Concurrent.PFold (pfoldA, Return (..))
import Text.Parsec.Prim hiding (Empty)
import Text.Parsec.Char
import Control.Monad (forM)
import Control.Monad.Trans (liftIO)

import Termlib.Utils (PrettyPrintable(..))
import qualified Termlib.Trs as Trs
import Termlib.Problem (strictTrs) 
import qualified Tct.Processor as P
import Tct.Processor.PPrint
import Tct.Certificate (certified, constant)
import qualified Tct.Processor.Standard as S
import Tct.Processor.Args
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances
import Tct.Processor.Parse

-- failure and success

data TrivialProof = Succeeded 
                  | Failed
                  | Empty Bool

instance P.Answerable TrivialProof where 
    answer Succeeded = P.YesAnswer
    answer Failed    = P.NoAnswer
    answer (Empty True)    = P.answerFromCertificate $ certified (constant,constant)
    answer (Empty False)   = P.NoAnswer

instance PrettyPrintable TrivialProof where 
    pprint Succeeded = text "Success"
    pprint Failed    = text "Fail"
    pprint (Empty True)  = text "Empty rules are trivially bounded"
    pprint (Empty False) = text "Empty strict component of the problem is NOT empty."

instance P.Verifiable TrivialProof where
    verify _ _ = P.verifyOK

data Fail = Fail deriving (Show)

instance S.Processor Fail where
    type S.ArgumentsOf Fail = Unit
    type S.ProofOf Fail     = TrivialProof
    name Fail               = "fail"
    instanceName _          = "fail"
    solve _ _               = return Failed
    description Fail        = ["Processor 'fail' always returns the answer 'No'."]
    arguments Fail          = Unit

data Success = Success deriving (Show)

instance S.Processor Success where
    type S.ArgumentsOf Success = Unit
    type S.ProofOf Success     = TrivialProof
    name Success               = "success"
    instanceName _             = "success"
    solve _ _                  = return Succeeded
    description Success        = ["Processor 'success' always returns the answer 'Yes'."]
    arguments   Success        = Unit

data EmptyRules = EmptyRules deriving (Show)

instance S.Processor EmptyRules where
    type S.ArgumentsOf EmptyRules = Unit
    type S.ProofOf EmptyRules     = TrivialProof
    name EmptyRules               = "empty"
    solve _ prob | Trs.isEmpty $ strictTrs prob = return $ Empty True
                 | otherwise                    = return $ Empty False
    description EmptyRules       = ["Processor 'empty' returns 'Yes(O(1),O(1))' if the strict component of the problem is empty."]
    arguments   EmptyRules       = Unit

failProcessor :: S.StdProcessor Fail
failProcessor = S.StdProcessor Fail

successProcessor :: S.StdProcessor Success
successProcessor = S.StdProcessor Success

emptyProcessor :: S.StdProcessor EmptyRules
emptyProcessor = S.StdProcessor EmptyRules

fail :: P.InstanceOf (S.StdProcessor Fail)
fail = S.StdProcessor Fail `S.withArgs` ()

success :: P.InstanceOf (S.StdProcessor Success)
success = S.StdProcessor Success `S.withArgs` ()

empty :: P.InstanceOf (S.StdProcessor EmptyRules)
empty = S.StdProcessor EmptyRules `S.withArgs` ()



-- if-then-else

data Ite g t e = Ite

data IteProof g t e = IteProof { guardProof  :: P.ProofOf g
                               , branchProof :: Either (P.ProofOf t) (P.ProofOf e) }

instance ( P.Answerable (P.ProofOf t)
         , P.Answerable (P.ProofOf e))
    => P.Answerable (IteProof g t e) where
      answer p = either P.answer P.answer $ branchProof p

instance ( P.Answerable (P.ProofOf g)
         , PrettyPrintable (P.ProofOf g)
         , PrettyPrintable (P.ProofOf t)
         , PrettyPrintable (P.ProofOf e)) 
    => PrettyPrintable (IteProof g t e) where
        pprint p = ppcond $+$ text "" $+$ ppbranch
            where ppcond   = text ("a) We first check the conditional [" ++ (if suc then "Success" else "Fail") ++ "]:")
                             $+$ (nest 3 $ pprint $ guardProof p)
                  ppbranch = text ("b) We continue with the " ++ (if suc then "then" else "else") ++ "-branch:")
                             $+$ (nest 3 $ either pprint pprint $ branchProof p)
                  suc      = P.succeeded $ guardProof p

instance ( P.Verifiable (P.ProofOf g)
         , P.Verifiable (P.ProofOf t)
         , P.Verifiable (P.ProofOf e) )
    => P.Verifiable (IteProof g t e) where 
        verify prob proof = P.verify prob  (guardProof proof) `P.andVerify` vfy (branchProof proof)
            where vfy (Left p)  = P.verify prob p
                  vfy (Right p) = P.verify prob p

instance ( P.Processor g
         , P.Answerable (P.ProofOf g)
         , P.Processor t
         , P.Processor e) 
    => P.Processor (Ite g t e) where
        type P.ProofOf (Ite g t e)    = IteProof g t e 
        data P.InstanceOf (Ite g t e) = IteInstance (P.InstanceOf g) (P.InstanceOf t) (P.InstanceOf e)
        name Ite = "if-then-else processor"
        instanceName (IteInstance g _ _) = "Branch on wether processor '" ++ P.instanceName g ++ "' succeeds"
        solve_ (IteInstance g t e) prob = do gproof <- P.solve g prob
                                             if P.succeeded gproof 
                                              then do bproof <- P.solve t prob
                                                      return $ IteProof { guardProof  = gproof
                                                                        , branchProof = Left bproof }
                                              else do bproof <- P.solve e prob
                                                      return $ IteProof { guardProof  = gproof
                                                                        , branchProof = Right bproof }

instance P.ParsableProcessor (Ite P.AnyProcessor P.AnyProcessor P.AnyProcessor) where
    description     Ite = ["This processor implements conditional branching."]
    synString       Ite = [ P.Token "if", P.PosArg 1, P.Token "then", P.PosArg 2, P.Token "else", P.PosArg 3]
    optArgs         Ite = []
    posArgs         Ite = [ (1, P.ArgDescr { P.adIsOptional = False
                                           , P.adName       = "guard-processor"
                                           , P.adDefault    = Nothing
                                           , P.adDescr      = "The guard of the condition"
                                           , P.adSynopsis   = domainName (Phantom :: Phantom (Proc P.AnyProcessor))})            
                          , (2, P.ArgDescr { P.adIsOptional = False
                                           , P.adName       = "then-processor"
                                           , P.adDefault    = Nothing
                                           , P.adDescr      = "The processor that is executed when the guard succeeds"
                                           , P.adSynopsis   = domainName (Phantom :: Phantom (Proc P.AnyProcessor))})             
                          , (3, P.ArgDescr { P.adIsOptional = False
                                           , P.adName       = "else-processor"
                                           , P.adDefault    = Nothing
                                           , P.adDescr      = "The processor that is executed when the guard fails"
                                           , P.adSynopsis   = domainName (Phantom :: Phantom (Proc P.AnyProcessor))}) ]
    parseProcessor_ Ite = do let pb s = try (string s) >> whiteSpace >> P.parseAnyProcessor
                             ginst <- pb "if"
                             whiteSpace
                             tinst <- pb "then"
                             whiteSpace
                             einst <- pb "else"
                             return $ IteInstance ginst tinst einst
    

ite :: P.InstanceOf g -> P.InstanceOf t -> P.InstanceOf e -> P.InstanceOf (Ite g t e)
ite = IteInstance

iteProcessor :: Ite P.AnyProcessor P.AnyProcessor P.AnyProcessor
iteProcessor = Ite


-- parallel combinators

data OneOf p = Best | Fastest | Sequentially deriving (Eq, Show)

data OneOfProof p = OneOfFailed (OneOf p) [P.Proof p]
                  | OneOfSucceeded (OneOf p) (P.Proof p)

instance P.Answerable (P.Proof p) => P.Answerable (OneOfProof p) where
    answer (OneOfFailed _ _)    = P.MaybeAnswer
    answer (OneOfSucceeded _ p) = P.answer p

instance P.Verifiable (P.Proof p) => P.Verifiable (OneOfProof p) where
    verify _    (OneOfFailed _ _)    = P.verifyOK
    verify prob (OneOfSucceeded _ p) = P.verify prob p

instance (P.Processor p) => PrettyPrintable (OneOfProof p) where
    pprint proof = case proof of 
                     (OneOfFailed _ failures) -> text "None of the processors succeeded."
                                                $+$ text "" 
                                                $+$ detailsFailed (enumeration' failures)
                     (OneOfSucceeded o p)     -> descr o
                                                $+$ text ""
                                                $+$ pprint (P.result p)
                                                    where descr Sequentially = procName p <+> text "succeeded:"
                                                          descr Fastest      = procName p <+> text "proved the goal fastest:"
                                                          descr Best         = procName p <+> text "proved the best result:"

instance (P.Processor p) => S.Processor (OneOf p) where
    type S.ArgumentsOf (OneOf p) = Arg [Proc p]
    type S.ProofOf (OneOf p)     = OneOfProof p

    name Fastest      = "fastest"
    name Sequentially = "sequentially"
    name Best         = "best"

    instanceName inst = c (S.processor inst) -- ++ " of " ++  (concat $ intersperse ", " [ "'" ++ P.instanceName p ++ "'" | p <- S.processorArgs inst])
        where c Best         = "Best"
              c Fastest      = "Fastest"
              c Sequentially = "Sequentially"

    description Best         = ["Processor 'Best' applies the given list of processors in parallel and returns the proof admitting the lowest complexity certificate."]
    description Fastest      = ["Processor 'Fastest' applies the given list of processors in parallel and returns the first successful proof."]
    description Sequentially = ["Processor 'Sequentially' applies the given list of processors sequentially and returns the first successful proof."]

    arguments _ = arg { A.name        = "subprocessors"
                      , A.description = "a list of subprocessors"}
    solve theproc prob | proc == Sequentially = solveSeq (S.processorArgs theproc) []
                       | proc == Best         = solveBest (S.processorArgs theproc)
                       | otherwise           = solveFast (S.processorArgs theproc)

        where proc = S.processor theproc 
              mkActions ps = forM ps $ \ proc -> P.mkIO $ P.apply proc prob
              ofResult o (Left faileds) = OneOfFailed o faileds
              ofResult o (Right proof) = OneOfSucceeded o proof
              
              solveSeq []     failures = return $ OneOfFailed Sequentially (reverse failures)
              solveSeq (p:ps) failures = do r <- P.apply p prob
                                            if P.succeeded r
                                             then return $ OneOfSucceeded Sequentially r
                                             else solveSeq ps (r:failures)
                                
              solveBest = solvePar betterThan final 
                  where p1 `betterThan` p2 = P.certificate p1 < P.certificate p2
                        final = const False

              solveFast= solvePar betterThan final
                  where _ `betterThan` _ = True
                        final = const True

              solvePar better final ps = do actions <- mkActions ps
                                            let sel (Left ps') proof | P.succeeded proof = ret proof
                                                                     | otherwise         = Continue $ Left (proof : ps')
                                                sel (Right p1) p2 | p1 `better` p2 = ret p1
                                                                  | otherwise      = ret p2
                                                ret proof | final proof = Stop $ Right proof
                                                          | otherwise   = Continue $ Right proof
                                            r <- liftIO $ pfoldA sel (Left []) actions
                                            return $ ofResult proc r




bestProcessor :: S.StdProcessor (OneOf P.AnyProcessor)
bestProcessor = S.StdProcessor Best

fastestProcessor :: S.StdProcessor (OneOf P.AnyProcessor)
fastestProcessor = S.StdProcessor Fastest

sequentiallyProcessor :: S.StdProcessor (OneOf P.AnyProcessor)
sequentiallyProcessor = S.StdProcessor Sequentially

best :: (P.Processor p) => [P.InstanceOf p] -> P.InstanceOf (S.StdProcessor (OneOf p))
best ps = S.StdProcessor Best `S.withArgs` ps

fastest :: (P.Processor p) => [P.InstanceOf p] -> P.InstanceOf (S.StdProcessor (OneOf p))
fastest ps = S.StdProcessor Fastest `S.withArgs` ps

sequentially :: (P.Processor p) => [P.InstanceOf p] -> P.InstanceOf (S.StdProcessor (OneOf p))
sequentially ps = S.StdProcessor Sequentially `S.withArgs` ps
