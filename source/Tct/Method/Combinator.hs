{-# LANGUAGE TypeSynonymInstances #-}
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
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveDataTypeable #-}

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
import Data.Typeable
import Text.PrettyPrint.HughesPJ hiding (parens)
import Data.List (intersperse)
import Control.Concurrent.PFold (pfold, fastestSatisfying)
import Text.Parsec.Prim
import Text.Parsec.Char
import Control.Monad (forM)
import Control.Monad.Trans (liftIO)

import Termlib.Utils (PrettyPrintable(..))

import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import Tct.Proof
import Tct.Processor.Args
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances ()
import Tct.Processor.Parse
import qualified Tct.Certificate as C

-- failure and success

data TrivialProof = Succeeded 
                  | Failed

instance Answerable TrivialProof where 
    answer Succeeded = YesAnswer
    answer Failed    = NoAnswer

instance PrettyPrintable TrivialProof where 
    pprint Succeeded = text "Success"
    pprint Failed    = text "Fail"

instance ComplexityProof TrivialProof

data Fail = Fail deriving (Show, Typeable)

instance S.StdProcessor Fail where
    type S.ArgumentsOf Fail = NoArgs
    type S.ProofOf Fail     = TrivialProof
    name Fail               = "fail"
    instanceName _          = "fail"
    solve _ _               = return Failed
    description Fail        = ["Processor 'fail' always returns the answer 'No'."]
    arguments Fail          = NoArgs

data Success = Success deriving (Show, Typeable)

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

data Ite g t e = Ite g t e

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


instance ( Answerable (P.ProofOf g)
         , Answerable (P.ProofOf t)
         , Answerable (P.ProofOf e)
         , PrettyPrintable (P.ProofOf g)
         , PrettyPrintable (P.ProofOf t)
         , PrettyPrintable (P.ProofOf e)) => ComplexityProof (IteProof g t e)

instance ( P.Processor g
         , Answerable (P.ProofOf g)
         , P.Processor t
         , P.Processor e) 
    => P.Processor (Ite g t e) where
        type P.ProofOf (Ite g t e)    = IteProof g t e 
        data P.InstanceOf (Ite g t e) = IteInstance (P.InstanceOf g) (P.InstanceOf t) (P.InstanceOf e)
        name (Ite _ _ _) = "if-then-else processor"
        instanceName (IteInstance g _ _) = "Branch on wether processor '" ++ P.instanceName g ++ "' succeeds"
        description  _   = ["This processor implements conditional branching."]
--        fromInstance (IteInstance instg instt inste)  = Ite (P.fromInstance instg) (P.fromInstance instt) (P.fromInstance inste)
        solve (IteInstance g t e) prob = do gproof <- P.solve g prob
                                            if succeeded gproof 
                                             then finish gproof Left t
                                             else finish gproof Right e
            where finish gproof d p = do bproof <- P.solve p prob
                                         return $ IteProof { guardProof  = gproof
                                                           , branchProof = d bproof }

instance ( P.ParsableProcessor g
         , Answerable (P.ProofOf g)
         , P.ParsableProcessor t
         , P.ParsableProcessor e) 
    => P.ParsableProcessor (Ite g t e) where
        synopsis        (Ite g t e) = "if " ++ P.synopsis g ++ " then " ++ P.synopsis t ++ " else " ++ P.synopsis e
        parseProcessor_ (Ite g t e) = do let pb s p = try (string s) >> whiteSpace >> P.parseProcessor p
                                         ginst <- pb "if" g
                                         whiteSpace
                                         tinst <- pb "then" t
                                         whiteSpace
                                         einst <- pb "else" e
                                         return $ IteInstance ginst tinst einst

ite :: P.InstanceOf g -> P.InstanceOf t -> P.InstanceOf e -> P.InstanceOf (Ite g t e)
ite = IteInstance

iteProcessor :: g -> t -> e -> (Ite g t e)
iteProcessor g t e = Ite g t e


-- parallel combinators

data OneOf = Best | Fastest | Sequentially deriving (Eq, Show, Typeable)

data OneOfProof = OneOfFailed OneOf
                | OneOfSucceeded OneOf P.SomeProof (P.InstanceOf P.AnyProcessor)

instance Answerable OneOfProof where
    answer (OneOfFailed _)        = MaybeAnswer
    answer (OneOfSucceeded _ p _) = answer p

instance PrettyPrintable OneOfProof where
    pprint (OneOfFailed _) = text "All processors failed"
    pprint (OneOfSucceeded _ proof _) = pprint proof -- text "Processor" <+> quotes (text $ P.instanceName proc) <+> text "has been applied:"
--                                           $+$ pprint proof
instance ComplexityProof OneOfProof

instance S.StdProcessor OneOf where
    type S.ArgumentsOf OneOf = Arg [S.Processor P.AnyProcessor]
    type S.ProofOf OneOf     = OneOfProof

    name Fastest      = "fastest"
    name Sequentially = "sequentially"
    name Best         = "best"

    instanceName inst = c (S.processor inst) ++ " of " ++  (concat $ intersperse ", " [ "'" ++ P.instanceName p ++ "'" | p <- S.processorArgs inst])
        where c Best         = "Best"
              c Fastest      = "Fastest"
              c Sequentially = "First successful"

    description Best         = ["Processor 'Best' applies the given list of processors in parallel and returns the proof admitting the lowest complexity certificate."]
    description Fastest      = ["Processor 'Fastest' applies the given list of processors in parallel and returns the first successful proof."]
    description Sequentially = ["Processor 'Fastest' applies the given list of processors sequentially and returns the first successful proof."]

    arguments _ = arg { A.name        = "subprocessors"
                      , A.description = "a list of subprocessors"}
    solve theproc prob | S.processor theproc == Sequentially = solveSeq (S.processorArgs theproc)
                       | S.processor theproc == Best         = solveBest (S.processorArgs theproc)
                       | otherwise                           = solveFast (S.processorArgs theproc)

        where mkActions ps = forM ps $ \ proc -> P.mkIO $ do proof <- P.solve proc prob
                                                             return $ Just (proof, proc)
              ofResult o Nothing = OneOfFailed o
              ofResult o (Just (proof, proc)) = OneOfSucceeded o proof proc
              
              solveSeq [] = return $ OneOfFailed Sequentially
              solveSeq (p:ps) = do r <- P.solve p prob
                                   if succeeded r
                                    then return $ OneOfSucceeded Sequentially r p
                                    else solveSeq ps
              
              solveFast ps = do actions <- mkActions ps
                                let msucceeded Nothing = False
                                    msucceeded (Just (proof, _)) = succeeded proof
                                r <- liftIO $ fastestSatisfying msucceeded Nothing actions
                                return $ ofResult Fastest r
                                
              solveBest ps = do actions <- mkActions ps
                                let mcertificate Nothing           = C.uncertified 
                                    mcertificate (Just (proof, _)) = certificate proof 
                                    select mpr1 mpr2 | mcertificate mpr1 > mcertificate mpr2 = mpr2
                                                     | otherwise                             = mpr1
                                r <- liftIO $ pfold select Nothing $ actions
                                return $ ofResult Best r




bestProcessor :: S.Processor OneOf
bestProcessor = S.Processor Best

fastestProcessor :: S.Processor OneOf
fastestProcessor = S.Processor Fastest

sequentiallyProcessor :: S.Processor OneOf
sequentiallyProcessor = S.Processor Sequentially

best :: [P.InstanceOf P.AnyProcessor] -> P.InstanceOf (S.Processor OneOf) -- TODO
best a = Best `S.calledWith` a

