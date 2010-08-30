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

module Tct.Method.Combinator 
    ( bestStrategy
    , fastestStrategy
    , sequentiallyStrategy
    , iteStrategy
    , failStrategy
    , succStrategy
    , best
    , fastest
    , sequentially
    , (.>>)
    , ite
    , fail
    , success
    )
where
import Prelude hiding (fail)
import Control.Concurrent.PFold (pfoldA, Return(..))
import Control.Monad.Trans
import Data.List (intersperse)
import Data.Typeable
import Text.ParserCombinators.Parsec
import Text.PrettyPrint.HughesPJ hiding (parens)

import qualified Termlib.Trs as Trs
import Termlib.Utils

import Tct.Certificate
import Tct.Processor
import Tct.Strategy
import Tct.Strategy.Flag (noFlags)
import Tct.Strategy.Parse (whiteSpace)
import Tct.Proof (certificate, succeeded, failed)
import qualified Tct.Proof as P


-- ^ Strategies

bestStrategy :: SomeStrategy
bestStrategy = SomeStrategy $ OneOfStrat Best

fastestStrategy :: SomeStrategy
fastestStrategy = SomeStrategy $ OneOfStrat Fastest

sequentiallyStrategy :: SomeStrategy
sequentiallyStrategy = SomeStrategy $ SeqStrategy

iteStrategy :: SomeStrategy
iteStrategy = SomeStrategy IteStrat

failStrategy :: SomeStrategy
failStrategy = SomeStrategy Fail

succStrategy :: SomeStrategy
succStrategy = SomeStrategy Succ

-- ^ Combinators

best :: forall a. Processor a => [a] -> OneOf
best as = OneOf [SomeProcessor a | a <- as] Best

fastest :: forall a. Processor a => [a] -> OneOf
fastest as = OneOf [SomeProcessor a | a <- as] Fastest

(.>>) :: (Processor a, Processor b) => a -> b -> Sequentially
a .>> b = Sequentially [SomeProcessor a, SomeProcessor b]

sequentially :: forall a. Processor a => [a] -> Sequentially
sequentially as = Sequentially [SomeProcessor a | a <- as]

ite :: (Processor g, Processor t, Processor e) => g -> t -> e -> Ite
ite g t e = Ite (SomeProcessor g) (SomeProcessor t) (SomeProcessor e)

fail :: Fail
fail = Fail

success :: Succ
success = Succ

-- Parallel combinator 
data OneOfCombine = Best | Fastest deriving (Show, Typeable)
data OneOf = OneOf [SomeProcessor] OneOfCombine deriving (Typeable)

data instance (ProofFrom OneOf) = forall proc proof. (Processor proc, P.ComplexityProof proof) => OneOfProof proof proc

instance PrettyPrintable (ProofFrom OneOf)   
    where pprint (OneOfProof p _) = pprint p
instance P.Proof (ProofFrom OneOf)           where succeeded (OneOfProof p _) = succeeded p
instance P.ComplexityProof (ProofFrom OneOf) where certificate (OneOfProof p _) = certificate p

instance Processor OneOf where 
  name i (OneOf l c) = n c ++ (concat $ intersperse ", " [ "'" ++ name (i - 1) p ++ "'"| p <- l])
      where n Best = "best of "
            n Fastest = "fastest of "
  solve (OneOf ps s) prob = 
      do r <- oneOfRun s betterThan $ oneOfMkActions apply prob ps
         case r of 
           Left l  -> abortWith $ oneOfMkFailMsg l
           Right (proof', proc') -> return $ OneOfProof proof' proc'
      where proof1 `betterThan` proof2 = certificate proof1 <= certificate proof2
  solvePartial proc@(OneOf ps s) prob = 
      do r <- oneOfRun s betterThan $ oneOfMkActions applyPartial prob ps
         case r of 
           Left l                        -> abortWith $ oneOfMkFailMsg l
           Right (Right proof', proc') -> return $ proof' { ppProof = OneOfProof (ppProof proof') proc' , ppProc = proc }

           _               -> error "Combinator.OneOf.solvePartial: failed proof succeeded"
      where (Right proof1) `betterThan` (Right proof2) | c1 < c2   = True
                                                       | c1 > c2   = False
                                                       | otherwise = n1 <= n2
                where c1 = certificate $ ppProof proof1
                      c2 = certificate $ ppProof proof2
                      n1 =  length $ Trs.toRules $ ppStrict proof1
                      n2 =  length $ Trs.toRules $ ppStrict proof2
            _               `betterThan` _                          = error "Combinator.OneOf.betterThan: called with failed proof"

oneOfMkActions :: (Processor proc, P.Proof proof, Monad m) => (proc -> prob -> m proof) -> prob -> [proc] -> [m (proof, proc)]
oneOfMkActions applyfn prob procs = [ applyfn sp prob >>= \ p -> return (p,sp)  | sp <- procs ]

oneOfMkFailMsg :: (Processor proc, P.Proof proof) => [(proof, proc)] -> Doc
oneOfMkFailMsg ls =  text "All processors failed. Below you can find the failed subproofs." 
                $++$ fsep [ ppHeading proc c $++$ (nest 2 $ pprint proof $+$ text "") | ((proof,proc), c) <- zip ls [(1::Int)..] ] 
    where ppHeading proc c = pprint c <> text ")" <+> text "Processor" <+> quotes (text $ name 3 proc) <+> text "failed due to the following reason(s):" 

oneOfRun :: (Processor proc, P.Proof proof) => OneOfCombine -> (proof -> proof -> Bool) -> [Solver (proof, proc)] -> Solver (Either [(proof, proc)] (proof, proc))
oneOfRun s betterThan solveActions = do slver <- getSatSolver
                                        liftIO $ pfoldA (combinator s) (Left []) [toIO slver sa | sa <- solveActions]
    where toIO slver a = do r <- runSolver slver a 
                            case r of 
                              Right e -> return e
                              Left _  -> error "Combinator.oneOfRun should not happen"
          combinator Best = betterOne 
          combinator Fastest = fastestOne
          betterOne (Left l) p@(proof,_) | failed proof = Continue $ Left $ p : l
                                         | otherwise    = Continue $ Right p
          betterOne (Right p1@(proof1,_)) p2@(proof2,_) | failed proof2 = Continue $ Right $ p1
                                                        | otherwise     = Continue $ Right $ if proof1 `betterThan` proof2 then p1 else p2
          fastestOne (Left l) p@(proof,_) | failed proof = Continue $ Left $ p : l
                                          | otherwise    = Stop $ Right p
          fastestOne _       _ = error "Combinator: -60 sec until explosion"
 
data OneOfStrat = OneOfStrat OneOfCombine deriving Show

instance Strategy OneOfStrat where 
  strategyName (OneOfStrat Best) = "best"
  strategyName (OneOfStrat Fastest) = "fastest"
  flags _ = noFlags
  description (OneOfStrat Best) = [unlines ["This processor applies a list of strategies in parallel and returns the 'best' proof."
                                           , "Usually the 'best' proof is the one admitting the lowest complexity."
                                           , "However, if applied in a relative setting, we additionally prefer those proofs that orient more rules strictly."]]
  description (OneOfStrat Fastest) = ["This processor applies a list of strategies in parallel and returns the first successful proof."]

  parseProcessor s@(OneOfStrat c)  = mkParseSomeProcessor s
                                   $ \ (_,ls) -> OneOf ls c
  synopsis p =  text (strategyName p) <+> text "[<strategy>]^+"




data Sequentially = Sequentially [SomeProcessor] deriving (Typeable)
data instance (ProofFrom Sequentially) = forall p. (P.ComplexityProof p) => SeqSucceeded p
                                       | forall p. (P.ComplexityProof p) => SeqFailed [p]


instance PrettyPrintable (ProofFrom Sequentially) where 
    pprint (SeqSucceeded p) = pprint p
    pprint (SeqFailed ps)    = text "None of the processors succeeded:"
                               $+$ text ""
                               $+$ vcat [ text [l] <> text ")" <+> pprint p | (p,l) <- zip ps ['a'..]]

instance P.Proof (ProofFrom Sequentially) where 
    succeeded (SeqSucceeded _) = True
    succeeded _                = False
instance P.ComplexityProof (ProofFrom Sequentially) where 
    certificate (SeqSucceeded p) = certificate p
    certificate _                = uncertified

instance Processor Sequentially where 
  name i (Sequentially l) =  "sequentially " ++ (concat $ intersperse ", " [name (i - 1) p | p <- l])
  solve (Sequentially ls) prob = slv ls []
      where slv []     fs = return $ SeqFailed $ reverse fs
            slv (p:ps) fs = do proof <- apply p prob
                               case succeeded proof of 
                                 True  -> return $ SeqSucceeded proof
                                 False -> slv ps (proof:fs)
 
data SeqStrategy = SeqStrategy deriving Show

instance Strategy SeqStrategy where 
  strategyName _    = "sequentially"
  flags _           = noFlags
  description _     = ["applies a list of strategies in sequentially, returns the first successful proof"]

  parseProcessor s  = mkParseSomeProcessor s $ \ (_,ls) -> Sequentially ls
  synopsis _        =  text "sequentially [<strategy>]^+"


data Ite = Ite SomeProcessor SomeProcessor SomeProcessor deriving (Typeable)

data instance (ProofFrom Ite) = forall proc1 proc2. (Processor proc1, Processor proc2) => 
                                IteProof (Erroneous (ProofFrom proc1))
                                         (Erroneous (ProofFrom proc2))


instance PrettyPrintable (ProofFrom Ite) where
  pprint (IteProof cond proof) = ppcond $+$ text "" $+$ ppbranch
    where ppcond   = text ("a) We first check the conditional [" ++ (if suc then "Success" else "Fail") ++ "]:")
                     $+$ (nest 3 $ pprint cond)
          ppbranch = text ("b) We continue with the " ++ (if suc then "then" else "else") ++ "-branch:")
                     $+$ (nest 3 $ pprint proof)
          suc      = succeeded cond
instance P.Proof (ProofFrom Ite)           where succeeded (IteProof _ proof)   = succeeded proof
instance P.ComplexityProof (ProofFrom Ite) where certificate (IteProof _ proof) = certificate proof

instance Processor Ite where
  name i (Ite c t e) = concat ["if ", name (i - 1) c, " then ", name (i - 1) t, " else ", name (i - 1) e]  
  solve (Ite c t e) prob = do cproof <- apply c prob
                              (if succeeded cproof 
                               then apply t prob 
                               else apply e prob) >>= mk cproof
                                where mk cproof proof = return $ IteProof (toErroneous cproof) (toErroneous proof)

data IteStrat = IteStrat deriving Show

instance Strategy IteStrat where 
  strategyName _ = "if"
  flags _ = noFlags
  description _ = ["if-then-else strategy"]
  parseProcessor _ = do c <- pb "if"
                        whiteSpace
                        t <- pb "then"
                        whiteSpace
                        e <- pb "else"
                        return $ SomeProcessor (Ite c t e)
    where pb s = try (string s) >> whiteSpace >> parseSomeProcessor
  synopsis _ =  text "if <strategy> then <strategy> else <strategy>"


data Fail = Fail deriving (Show, Typeable)
data instance (ProofFrom Fail) = Failed
instance PrettyPrintable (ProofFrom Fail)   where pprint _      = text "Failed"
instance P.Proof (ProofFrom Fail)           where succeeded _   = False
instance P.ComplexityProof (ProofFrom Fail) where certificate _ = uncertified
instance Processor Fail where 
   name _ _ = "Fail"
   solve _ _ = abortWith $ text "Processor " <+> quotes (text "Fail") <+> text "always fails"

instance Strategy Fail where
  strategyName _ = "fail"
  flags _ = noFlags
  description _ = ["the strategy that always fails"]
  parseProcessor s = mkParseSomeProcessor s $ \ (_,()) -> Fail


data Succ = Succ deriving (Show, Typeable)
data instance (ProofFrom Succ) = Succeed
instance PrettyPrintable (ProofFrom Succ)   where pprint _      = text "Processor " <+> quotes (text "succ") <+> text "always succeeds"
instance P.Proof (ProofFrom Succ)           where succeeded _   = True
instance P.ComplexityProof (ProofFrom Succ) where certificate _ = uncertified
instance Processor Succ where 
   name _ _ = "Succeed"
   solve _ _ = return Succeed

instance Strategy Succ where
  strategyName _ = "succ"
  flags _ = noFlags
  description _ = ["the strategy that always succeeds"]
  parseProcessor s = mkParseSomeProcessor s $ \ (_,()) -> Succ

