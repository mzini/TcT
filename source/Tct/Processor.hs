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

{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Tct.Processor
    ( SatSolver (..)
    , Processor (..)
    , ParsableProcessor (..)
    , Proof (..)
    , SolverM (..)
    , SolverState (..)
    , StdSolverM
    , ProcessorParser
    , apply
    , evalList
    , evalList'
    , parseProcessor
    , fromString
    -- * Some Processor
    , SomeProcessor
    , SomeProof
    , SomeInstance
    , someProof
    , someProcessor
    , someInstance
    , solveBy
    -- * Any Processor
    , AnyProcessor
    , none
--    , anyOf
    , (<|>)
    , processors
    , parseAnyProcessor
    ) 
where

import Control.Monad.Error
import Control.Monad.Reader
import Control.Concurrent.PFold (pfoldA, Return(..))
import Data.Typeable

import qualified Qlogic.SatSolver as SatSolver
import Qlogic.SatSolver (Decoder)
import Qlogic.MiniSat (setCmd, MiniSat)
import Text.ParserCombinators.Parsec (CharParser, ParseError, getState, choice)
import qualified Text.ParserCombinators.Parsec as Parsec
import Text.PrettyPrint.HughesPJ hiding (parens)

import Termlib.Problem
import Termlib.Utils (PrettyPrintable(..), paragraph, ($++$))
import Tct.Processor.Parse hiding (fromString)
import qualified Tct.Processor.Parse as Parse
import qualified Tct.Proof as P


data SatSolver = MiniSat FilePath

-- solver

class MonadIO m => SolverM m where
    type St m
    mkIO :: m a -> m (IO a)
    runSolver :: St m -> m a -> IO a
    minisatValue :: (Decoder e a) => MiniSat () -> e -> m (Maybe e)
    solve :: (Processor a) => InstanceOf a -> Problem -> m (ProofOf a)
-- TODO needs to be redone after qlogic-update, allow generic solvers
                                
-- processor

class P.ComplexityProof (ProofOf a) => Processor a where
    type ProofOf a                  
    data InstanceOf a 
    name            :: a -> String
    instanceName    :: (InstanceOf a) -> String
    solve_          :: SolverM m => InstanceOf a -> Problem -> m (ProofOf a)


type ProcessorParser a = CharParser AnyProcessor a 

-- proof

data Proof proc = Proof { appliedProcessor :: InstanceOf proc
                        , inputProblem     :: Problem 
                        , result           :: ProofOf proc}


instance (Processor proc) => PrettyPrintable (Proof proc) where
    pprint p@(Proof inst prob res) = ppheading $++$ ppres
        where ppheading = (pphead $+$ underline) $+$ ppanswer $+$ ppinput
              pphead    = quotes (text (instanceName inst))
              ppres     = pt "Proof Output" $+$ nest 2 (pprint res)
              ppinput   = pt "Input Problem" <+> measureName prob <+> text "with respect to"
                          $+$ nest 2 (prettyPrintRelation prob)
              ppanswer  = pt "Answer" <+> pprint (P.answer p)
              underline = text (take (length $ show pphead) $ repeat '-')
              pt s = wtext 17 $ s ++  ":"
              wtext i s = text $ take n $ s ++ repeat ' ' where n = max i (length s)

instance (P.Answerable (ProofOf proc)) => P.Answerable (Proof proc) where
    answer p = P.answer (result p)

-- instance (P.ComplexityProof (ProofOf proc), Processor proc) => P.ComplexityProof (Proof proc)


-- operations

apply :: (SolverM m, Processor proc) => (InstanceOf proc) -> Problem -> m (Proof proc)
apply proc prob = solve proc prob >>= mkProof
    where mkProof = return . Proof proc prob

evalList :: (SolverM m) => Bool -> (a -> Bool) -> [m a] -> m (Either (a,[a]) [a])
evalList True success ms  = do actions <- sequence [ mkIO $ m | m <- ms]
                               liftIO $ pfoldA comb (Right []) actions
    where comb (Right as) a | success a = Continue $ Right $ a : as
                            | otherwise       = Stop $ Left (a,as)
evalList False _     []       = return $ Right []
evalList False success (m : ms) = do a <- m
                                     if success a
                                      then do eas <- evalList False success ms
                                              return $ case eas of {Right as -> Right (a:as); Left (f,as) -> Left (f,a:as)}
                                      else return $ Left (a,[])

evalList' :: (SolverM m) => Bool -> [m a] -> m [a]
evalList' b ms = do Right rs <- evalList b (const True) ms
                    return rs

-- parsable processor

class Processor a => ParsableProcessor a where
    synopsis :: a -> String
    description     :: a -> [String]
    argDescriptions :: a -> [(String, String)]
    argDescriptions _ = []
    parseProcessor_ :: a -> ProcessorParser (InstanceOf a)


parseProcessor :: ParsableProcessor a => a -> ProcessorParser (InstanceOf a)
parseProcessor a = parens parse Parsec.<|> parse
    where parse = parseProcessor_ a

fromString :: ParsableProcessor p => AnyProcessor -> p -> String -> Either ParseError (InstanceOf p)
fromString a p s = Parse.fromString (parseProcessor p) a "supplied strategy" s


-- someprocessor, anyprocessor

data SomeProcessor = forall p. (P.ComplexityProof (ProofOf p) , ParsableProcessor p) => SomeProcessor p 
data SomeProof     = forall p. (P.ComplexityProof p) => SomeProof p
data SomeInstance  = forall p. (P.ComplexityProof (ProofOf p) , Processor p) => SomeInstance (InstanceOf p)


instance PrettyPrintable SomeProof where pprint (SomeProof p) = pprint p
instance P.Answerable SomeProof where answer (SomeProof p) = P.answer p

instance Typeable (InstanceOf SomeProcessor) where 
    typeOf (SPI _) = mkTyConApp (mkTyCon "Tct.Processor.SPI") [mkTyConApp (mkTyCon "SomeInstance") []]

instance Processor SomeProcessor where
    type ProofOf    SomeProcessor = SomeProof
    data InstanceOf SomeProcessor = SPI SomeInstance
    name (SomeProcessor proc)                = name proc
    instanceName (SPI (SomeInstance inst))   = instanceName inst
    solve_ (SPI (SomeInstance inst)) prob    = SomeProof `liftM` solve_ inst prob

instance ParsableProcessor SomeProcessor where
    synopsis (SomeProcessor proc) = synopsis proc
    parseProcessor_ (SomeProcessor proc) = (SPI . SomeInstance) `liftM` parseProcessor_ proc
    description (SomeProcessor proc)         = description proc
    argDescriptions (SomeProcessor proc)     = argDescriptions proc

instance PrettyPrintable SomeProcessor where
    pprint (SomeProcessor proc) = (ppheading $+$ underline) $$ (nest 2 $ ppsyn $++$ ppdescr $++$ ppargdescr)
        where ppheading = (text "Processor" <+> doubleQuotes (text sname) <> text ":")
              underline = text (take (length $ show ppheading) $ repeat '-')
              ppdescr   = block "Description" $ vcat [paragraph s | s <- descr]
              ppsyn     = block "Usage" $ text (synopsis proc)
              ppargdescr | length l == 0 = empty
                         | otherwise     = block "Arguments" $ vcat l
                  where l = [text nm <> text ":" <+> paragraph s | (nm, s) <- argDescriptions proc]
              sname = name proc 
              descr = description proc 
              block n d = text n <> text ":" $+$ nest 1 d

instance Show (InstanceOf SomeProcessor) where 
    show _ = "InstanceOf SomeProcessor"

someProof :: (P.ComplexityProof p) => p -> SomeProof
someProof = SomeProof

someProcessor :: (P.ComplexityProof (ProofOf p), ParsableProcessor p) => p -> SomeProcessor
someProcessor = SomeProcessor

someInstance :: forall p. (P.ComplexityProof (ProofOf p), Processor p) => InstanceOf p -> InstanceOf SomeProcessor
someInstance inst = SPI (SomeInstance inst)

solveBy :: (Processor a, SolverM m) => Problem -> InstanceOf a -> m SomeProof
prob `solveBy` proc = someProof `liftM` solve proc prob



-- anyInstance :: forall p. (P.ComplexityProof (ProofOf p), Processor p) => InstanceOf p -> SomeInstance
-- anyInstance inst = SPI (SomeInstance inst)

data AnyProcessor = OO String [SomeProcessor]

instance Processor AnyProcessor where
    type ProofOf AnyProcessor    = SomeProof
    data InstanceOf AnyProcessor = OOI (InstanceOf SomeProcessor)
    name (OO s _)           = s
    instanceName (OOI inst) = instanceName inst
    solve_ (OOI inst) prob  = solve_ inst prob

instance Typeable (InstanceOf AnyProcessor) where 
    typeOf (OOI _) = mkTyConApp (mkTyCon "Tct.Processor.OOI") [mkTyConApp (mkTyCon "SomeInstance") []]

instance ParsableProcessor AnyProcessor where
    synopsis _    = "<processor>"
    description _           = []
    argDescriptions _       = []
    parseProcessor_ (OO _ ps) = do inst <- choice [ parseProcessor p' | p' <- ps]
                                   return $ OOI inst

instance Show (InstanceOf AnyProcessor) where
    show _ = "InstanceOf AnyProcessor"

infixr 5 <|>
(<|>) :: (P.ComplexityProof (ProofOf p), ParsableProcessor p) => p -> AnyProcessor -> AnyProcessor
p <|> OO s l = OO s $ someProcessor p : l


none :: AnyProcessor
none = OO "any processor" []

processors :: AnyProcessor -> [SomeProcessor]
processors (OO _ l) = l

parseAnyProcessor :: ProcessorParser (InstanceOf AnyProcessor)
parseAnyProcessor = do a <- getState
                       parseProcessor a


-- basic solver monad
data SolverState = SolverState SatSolver
newtype StdSolverM r = S {runS :: ReaderT SolverState IO r }
    deriving (Monad, MonadIO, MonadReader SolverState)

instance SolverM StdSolverM where 
    type St StdSolverM = SolverState
    mkIO m = do s <- ask
                return $ runSolver s m

    runSolver slver m = runReaderT (runS m) slver

    minisatValue m e =  do SolverState slver <- ask
                           r <- liftIO $ val slver
                           case r of 
                             Right v -> return $ Just v
                             Left  _ -> return Nothing
        where val (MiniSat s) = SatSolver.value (setCmd s >> m) e 

    solve = solve_

