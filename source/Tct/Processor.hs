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

{-# LANGUAGE DeriveDataTypeable #-}
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
    , LSolverState (..)
    , StdSolverM
    , LoggingSolverM (..)
    , ProcessorParser
    , apply
    , parseProcessor
    , fromString
    -- * Some Processor
    , SomeProcessor
    , SomeProof
    , SomeInstance
    , some
    , someInstance
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
import Control.Concurrent.Chan
import System.CPUTime (getCPUTime)
import System.IO (Handle, hPutStrLn, hFlush)
import Control.Concurrent (ThreadId, forkIO, killThread, myThreadId)
import qualified Control.Exception as C
import Control.Monad.Reader
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
    solve :: (SolverM m, Processor a) => InstanceOf a -> Problem -> m (ProofOf a)
-- TODO needs to be redone after qlogic-update, allow generic solvers
                                
-- processor

class Processor a where
    type ProofOf a                  
    data InstanceOf a 
    name            :: a -> String
    instanceName    :: (InstanceOf a) -> String
    description     :: a -> [String]
    argDescriptions :: a -> [(String, String)]
    argDescriptions _ = []
--    fromInstance :: (InstanceOf a) -> a
    solve_          :: SolverM m => InstanceOf a -> Problem -> m (ProofOf a)

type ProcessorParser a = CharParser AnyProcessor a 

class Processor a => ParsableProcessor a where
    synopsis :: a -> String
    parseProcessor_ :: a -> ProcessorParser (InstanceOf a)


parseProcessor :: ParsableProcessor a => a -> ProcessorParser (InstanceOf a)
parseProcessor a = parens parse Parsec.<|> parse
    where parse = parseProcessor_ a


-- proof

data Proof proc = Proof { appliedProcessor :: InstanceOf proc
                        , inputProblem     :: Problem 
                        , result           :: ProofOf proc}

instance (Show (InstanceOf proc), Show (ProofOf proc)) => Show (Proof proc) where
    show (Proof proc prob res) = "Proof (" ++ show proc ++ ") (" ++ show prob ++ ") (" ++ show res ++ ")"

instance (P.ComplexityProof (ProofOf proc), Processor proc) => PrettyPrintable (Proof proc) where
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

instance (P.ComplexityProof (ProofOf proc), Processor proc, Show (InstanceOf proc)) 
    => P.ComplexityProof (Proof proc)

apply :: (SolverM m, Processor proc) => (InstanceOf proc) -> Problem -> m (Proof proc)
apply proc prob = solve proc prob >>= mkProof
    where mkProof = return . Proof proc prob


fromString :: ParsableProcessor p => AnyProcessor -> p -> String -> Either ParseError (InstanceOf p)
fromString a p s = Parse.fromString (parseProcessor p) a "supplied strategy" s

data SomeProcessor = forall p. (P.ComplexityProof (ProofOf p) , ParsableProcessor p) => SomeProcessor p 
data SomeProof     = forall p. (P.ComplexityProof p) => SomeProof p
data SomeInstance  = forall p. (P.ComplexityProof (ProofOf p) , Processor p) => SomeInstance (InstanceOf p) deriving Typeable


-- instance Show SomeProof where show (SomeProof p) = "SomeProof (" ++ show p ++ ")"
instance PrettyPrintable SomeProof where pprint (SomeProof p) = pprint p
instance P.Answerable SomeProof where answer (SomeProof p) = P.answer p

instance P.ComplexityProof SomeProof

instance Typeable (InstanceOf SomeProcessor) where 
    typeOf (SPI i) = mkTyConApp (mkTyCon "Tct.Processor.SPI") [typeOf i]

instance Processor SomeProcessor where
    type ProofOf    SomeProcessor = SomeProof
    data InstanceOf SomeProcessor = SPI SomeInstance
    name (SomeProcessor proc)                = name proc
    instanceName (SPI (SomeInstance inst))   = instanceName inst
    description (SomeProcessor proc)         = description proc
    argDescriptions (SomeProcessor proc)     = argDescriptions proc
    solve_ (SPI (SomeInstance inst)) prob    = SomeProof `liftM` solve_ inst prob
--    fromInstance (SPI (SomeInstance proc _)) = SomeProcessor proc

instance ParsableProcessor SomeProcessor where
    synopsis (SomeProcessor proc) = synopsis proc
    parseProcessor_ (SomeProcessor proc) = (SPI . SomeInstance) `liftM` parseProcessor_ proc

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

some :: (P.ComplexityProof (ProofOf p), ParsableProcessor p) => p -> SomeProcessor
some = SomeProcessor

someInstance :: forall p. (P.ComplexityProof (ProofOf p), Processor p) => InstanceOf p -> InstanceOf SomeProcessor
someInstance inst = SPI (SomeInstance inst)


data AnyProcessor = OO String [SomeProcessor] deriving Typeable

instance Processor AnyProcessor where
    type ProofOf AnyProcessor    = SomeProof
    data InstanceOf AnyProcessor = OOI (InstanceOf SomeProcessor)
    name (OO s _)           = s
    instanceName (OOI inst) = instanceName inst
    description _           = []
    argDescriptions _       = []
    solve_ (OOI inst) prob  = solve_ inst prob
--     fromInstance (OOI inst (OO _ l)) = OO (name $ fromInstance inst) l

instance Typeable (InstanceOf AnyProcessor) where 
    typeOf (OOI i) = mkTyConApp (mkTyCon "Tct.Processor.OOI") [typeOf i]

instance ParsableProcessor AnyProcessor where
    synopsis _    = "<processor>"
    parseProcessor_ (OO _ ps) = do inst <- choice [ parseProcessor p' | p' <- ps] -- look ahead to long...
                                   return $ OOI inst

instance Show (InstanceOf AnyProcessor) where
    show _ = "InstanceOf <anyprocessor>"

infixr 5 <|>
(<|>) :: (P.ComplexityProof (ProofOf p), ParsableProcessor p) => p -> AnyProcessor -> AnyProcessor
p <|> OO s l = OO s $ some p : l


none :: AnyProcessor
none = OO "any processor" []
-- anyOf :: [SomeProcessor] -> AnyProcessor
-- anyOf = OO

processors :: AnyProcessor -> [SomeProcessor]
processors (OO _ l) = l

parseAnyProcessor :: ProcessorParser (InstanceOf AnyProcessor)
parseAnyProcessor = do a <- getState
                       parseProcessor a

-- toSomeInstance :: InstanceOf AnyProcessor -> SomeInstance
-- toSomeInstance (OOI (SPI p)) = p

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

-- add logging to solver monad
data LoggingSig = LMStart | LMFin
data LoggingMsg = LoggingMsg LoggingSig Integer String ThreadId 

instance Show LoggingMsg where 
    show (LoggingMsg m t n pid) = "[" ++ show t ++ "]@" ++ show pid ++ ": Processor " ++ n ++ " " ++ sig m
        where sig LMStart = "started"
              sig LMFin   = "finished"

newtype LoggingSolverM m r = LS { runLS :: ReaderT (Chan LoggingMsg) m r}
    deriving (Monad, MonadIO, MonadReader (Chan LoggingMsg), MonadTrans)


data LSolverState st = LSolverState { subState  :: st
                                    , logHandle :: Handle }

instance SolverM m => SolverM (LoggingSolverM m) where 
    type St (LoggingSolverM m) = LSolverState (St m)

    mkIO m = do chan <- ask
                lift $ mkIO $ runReaderT (runLS m) chan

    runSolver st m = do chan <- liftIO $ newChan
                        let logThread = do msg <- readChan chan
                                           let handle = logHandle st
                                           hPutStrLn handle (show msg)
                                           hFlush handle
                                           logThread
                            run = const $ C.unblock $ runSolver (subState st) $ runReaderT (runLS m) chan
                        C.bracket (forkIO logThread) (\ pid -> putStrLn "killing" ) run

    minisatValue m e = lift $ minisatValue m e 
                       
    solve proc prob = do sendMsg LMStart
                         r <- solve_ proc prob -- HMN
                         sendMsg LMFin
                         return r
        where sendMsg sig = do t <- liftIO getCPUTime
                               let n = instanceName proc
                               pid <- liftIO $ myThreadId
                               chan <- ask
                               liftIO $ writeChan chan (LoggingMsg sig t n pid)
