{-# LANGUAGE UndecidableInstances #-}
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
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Tct.Processor
    ( SatSolver (..)
    , Processor (..)
    , Proof (..)
    , SolverM (..)
    , ProcessorParser
    , apply
    , mkIO
    , runSolver 
    , parseProcessor
    , minisatValue
    , getSatSolver
    , fromString)
where

import Control.Monad.Error
import Control.Monad.Reader

import qualified Qlogic.SatSolver as SatSolver
import Qlogic.SatSolver (Decoder)
import Qlogic.MiniSat (setCmd, MiniSat)
import Text.ParserCombinators.Parsec (CharParser, (<|>), ParseError)
import Text.PrettyPrint.HughesPJ hiding (parens)

import Termlib.Problem
import Termlib.Utils (PrettyPrintable(..))
import Tct.Processor.Parse hiding (fromString)
import qualified Tct.Processor.Parse as Parse
import qualified Tct.Proof as P

type ProcessorParser a = CharParser () a 

data SolverState = SolverState SatSolver
data SatSolver = MiniSat FilePath

newtype SolverM r = S {runS :: ReaderT SolverState IO r }
    deriving (Monad, MonadIO, MonadReader SolverState)


class Processor a where
    type ProofOf a                  
    data InstanceOf a 
    name  :: a -> String
    description :: a -> [String]
    synopsis :: a -> String
    fromInstance :: (InstanceOf a) -> a
    solve :: InstanceOf a -> Problem -> SolverM (ProofOf a)
    parseProcessor_ :: a -> ProcessorParser (InstanceOf a)


parseProcessor :: Processor a => a -> ProcessorParser (InstanceOf a)
parseProcessor a = parens parse <|> parse
    where parse = parseProcessor a


getSatSolver :: SolverM SatSolver
getSatSolver = do SolverState ss <- ask
                  return ss

runSolver_ :: SolverState -> SolverM a -> IO a
runSolver_ slver m = runReaderT (runS m) slver

runSolver :: SatSolver -> SolverM a -> IO a
runSolver s = runSolver_ (SolverState s)

mkIO :: SolverM a -> SolverM (IO a)
mkIO m = do s <- ask
            return $ runSolver_ s m

minisatValue :: (Decoder e a) => MiniSat () -> e -> SolverM (Maybe e)
minisatValue m e =  do slver <- getSatSolver
                       r <- liftIO $ val slver
                       case r of 
                         Right v -> return $ Just v
                         Left  _ -> return Nothing
    where val (MiniSat s) = SatSolver.value (setCmd s >> m) e 


data Proof proc = Proof { appliedProcessor :: InstanceOf proc
                        , inputProblem     :: Problem 
                        , result           :: ProofOf proc}

instance ( P.ComplexityProof (ProofOf proc), Processor proc) => PrettyPrintable (Proof proc) where
    pprint p@(Proof inst prob res) = ppheading $+$ text "" $+$ ppres
        where proc      = fromInstance inst
              ppheading = (pphead $+$ underline) $+$ ppanswer $+$ ppinput
              pphead    = quotes (text (name proc))
              ppres     = pt "Details" $+$ nest 2 (pprint res)
              ppinput   = pt "Input Problem" <+> measureName prob <+> text "with respect to"
                          $+$ nest 2 (prettyPrintRelation prob)
              ppanswer  = pt "Answer" <+> pprint (P.answer p)
              underline = text (take (length $ show pphead) $ repeat '-')
              pt s = wtext 17 $ s ++  ":"
              wtext i s = text $ take n $ s ++ repeat ' ' where n = max i (length s)

instance (P.Answerable (ProofOf proc)) => P.Answerable (Proof proc) where
    answer p = P.answer (result p)

instance (P.ComplexityProof (ProofOf proc), Processor proc) => P.ComplexityProof (Proof proc)

apply :: Processor proc => (InstanceOf proc) -> Problem -> SolverM (Proof proc)
apply proc prob = solve proc prob >>= mkProof
    where mkProof = return . Proof proc prob


fromString :: Processor p => p -> String -> Either ParseError (InstanceOf p)
fromString p s = Parse.fromString (parseProcessor p) () "supplied strategy" s

