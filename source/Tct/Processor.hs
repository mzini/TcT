{-# LANGUAGE ExistentialQuantification #-}
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
    , ParsableProcessor (..)
    , Proof (..)
    , SolverM (..)
    , ProcessorParser
    , apply
    , mkIO
    , runSolver 
    , parseProcessor
    , minisatValue
    , getSatSolver
    , fromString
    , SomeProcessor
    , AnyProcessor
    , some
    , someInstance
    , anyOf
    , processors
    , parseAnyProcessor
    ) 
where

import Control.Monad.Error
import Control.Monad.Reader

import qualified Qlogic.SatSolver as SatSolver
import Qlogic.SatSolver (Decoder)
import Qlogic.MiniSat (setCmd, MiniSat)
import Text.ParserCombinators.Parsec (CharParser, (<|>), ParseError, getState, choice)
import Text.PrettyPrint.HughesPJ hiding (parens)

import Termlib.Problem
import Termlib.Utils (PrettyPrintable(..))
import Tct.Processor.Parse hiding (fromString)
import qualified Tct.Processor.Parse as Parse
import qualified Tct.Proof as P


type ProcessorParser a = CharParser AnyProcessor a 
data SolverState = SolverState SatSolver
data SatSolver = MiniSat FilePath
newtype SolverM r = S {runS :: ReaderT SolverState IO r }
    deriving (Monad, MonadIO, MonadReader SolverState)

class Processor a where
    type ProofOf a                  
    data InstanceOf a 
    name  :: a -> String
    description :: a -> [String]
    fromInstance :: (InstanceOf a) -> a
    solve :: InstanceOf a -> Problem -> SolverM (ProofOf a)

class Processor a => ParsableProcessor a where
    synopsis :: a -> String
    parseProcessor_ :: a -> ProcessorParser (InstanceOf a)


parseProcessor :: ParsableProcessor a => a -> ProcessorParser (InstanceOf a)
parseProcessor a = parens parse <|> parse
    where parse = parseProcessor_ a


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


fromString :: ParsableProcessor p => AnyProcessor -> p -> String -> Either ParseError (InstanceOf p)
fromString a p s = Parse.fromString (parseProcessor p) a "supplied strategy" s


data SomeProcessor = forall p. (P.ComplexityProof (ProofOf p) , ParsableProcessor p) => SomeProcessor p 
data SomeProof     = forall p. (P.ComplexityProof p) => SomeProof p
data SomeInstance  = forall p. (P.ComplexityProof (ProofOf p) , ParsableProcessor p) => SomeInstance p (InstanceOf p)

instance PrettyPrintable SomeProof where
    pprint (SomeProof p) = pprint p

instance P.Answerable SomeProof where
    answer (SomeProof p) = P.answer p

instance P.ComplexityProof SomeProof

instance Processor SomeProcessor where
    type ProofOf    SomeProcessor = SomeProof
    data InstanceOf SomeProcessor = SPI SomeInstance
    name (SomeProcessor proc) = name proc
    description (SomeProcessor proc) = description proc
    solve (SPI (SomeInstance _ inst)) prob = SomeProof `liftM` solve inst prob
    fromInstance (SPI (SomeInstance proc _)) = SomeProcessor proc

instance ParsableProcessor SomeProcessor where
    synopsis (SomeProcessor proc) = synopsis proc
    parseProcessor_ (SomeProcessor proc) = (SPI . SomeInstance proc) `liftM` parseProcessor_ proc

instance PrettyPrintable SomeProcessor where
    pprint (SomeProcessor proc) = ppheading $$ (nest 2 $ ppdescr $+$ text "" $+$ ppsyn)
        where ppheading = text "Strategy" <+> doubleQuotes (text sname) <> text ":"
              ppdescr = vcat [fsep $ [text w | w <- words s] | s <- descr] 
              ppsyn = text "Usage:" $+$ text "" $+$  (nest 2 $ text $ synopsis proc)
              sname = name proc 
              descr = description proc 

some :: forall p. (P.ComplexityProof (ProofOf p), ParsableProcessor p) => p -> SomeProcessor
some = SomeProcessor

someInstance :: forall p. (P.ComplexityProof (ProofOf p), ParsableProcessor p) => InstanceOf p -> InstanceOf SomeProcessor
someInstance inst = SPI (SomeInstance (fromInstance inst) inst)


-- any processor
data AnyProcessor = OO [SomeProcessor]
instance Processor AnyProcessor where
    type ProofOf AnyProcessor = SomeProof
    data InstanceOf AnyProcessor = OOI (InstanceOf SomeProcessor) AnyProcessor
    name _ = "some processor" -- TODO
    description _ = []
    solve (OOI inst _) prob = solve inst prob
    fromInstance (OOI _ proc) = proc

instance ParsableProcessor AnyProcessor where
    synopsis _    = "" -- TODO
    parseProcessor_ p@(OO ps) = do inst <- choice [ parseProcessor p' | p' <- ps]
                                   return $ OOI inst p

anyOf :: [SomeProcessor] -> AnyProcessor
anyOf = OO

processors :: AnyProcessor -> [SomeProcessor]
processors (OO l) = l

parseAnyProcessor :: ProcessorParser (InstanceOf AnyProcessor)
parseAnyProcessor = do a <- getState
                       parseProcessor a