
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
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_HADDOCK prune #-}

module Tct.Processor
    ( SatSolver (..)
    , Processor (..)
    , ParsableProcessor (..)
    , Proof (..)
    , PartialProof (..)
    , progressed
    , SolverM (..)
    , SolverState (..)
    , StdSolverM
    , ProcessorParser
    , ArgDescr (..)
    , apply
    , evalList
    , evalList'
    , parseProcessor
    , fromString
      -- * Proofs 
    , PPMode (..)
    , ComplexityProof (..)
    , Answer (..)
    , succeeded
    , failed
    , isTimeout
    , certificate
    , answerFromCertificate
    -- * Some Processor
    , SomeProcessor (..)
    , SomeProof (..)
    , SomeInstance (..)
    , liftOOI
    , someProof
    , someProcessorProof
    , someProofNode
    , someProcessor
    , someInstance
    , solveBy
    -- * Any Processor
    , AnyProcessor
    , none
--    , anyOf
    , (<|>)
    , (<++>)
    , toProcessorList
    , fromProcessorList
    , parseAnyProcessor
    -- * Machine Readable Description of Processors
    , SynElt (..)
    , mrSynopsis
    -- * Default Options
    , IsDefaultOption (..)
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
import Termlib.Utils (PrettyPrintable(..), paragraph, ($++$), qtext)
import qualified Termlib.Utils as Utils
import Termlib.Rule (Rule)
import Tct.Certificate
import Tct.Processor.Parse hiding (fromString)
import qualified Tct.Processor.Parse as Parse

data SatSolver = MiniSat FilePath

-- * The Solver Monad

class MonadIO m => SolverM m where
    type St m
    runSolver    :: St m -> m a -> IO a
    mkIO         :: m a -> m (IO a)
    satSolver    :: m SatSolver
    minisatValue :: (Decoder e a) => MiniSat () -> e -> m (Maybe e)
    solve        :: (Processor proc) => InstanceOf proc -> Problem -> m (ProofOf proc)
    solvePartial :: (Processor proc) => InstanceOf proc -> [Rule] -> Problem -> m (PartialProof (ProofOf proc))
-- TODO needs to be redone after qlogic-update, allow generic solvers

-- ** Basic Solver Monad Implementation

data SolverState = SolverState SatSolver
newtype StdSolverM r = S {runS :: ReaderT SolverState IO r }
    deriving (Monad, MonadIO, MonadReader SolverState)

instance SolverM StdSolverM where 
    type St StdSolverM = SolverState
    mkIO m            = do s <- ask
                           return $ runSolver s m
    satSolver         = do SolverState s <- ask
                           return s
    runSolver slver m = runReaderT (runS m) slver
    minisatValue m e  = do SolverState slver <- ask
                           r <- liftIO $ val slver
                           case r of 
                             Right v -> return $ Just v
                             Left  _ -> return Nothing
        where val (MiniSat s) = SatSolver.value (setCmd s >> m) e 
    solve             = solve_
    solvePartial      = solvePartial_
                                
-- processor

data PPMode = StrategyOutput | ProofOutput deriving (Show, Eq, Ord)

class ComplexityProof proof where
    answer :: proof -> Answer
    pprintProof :: proof -> PPMode -> Doc
    

class (ComplexityProof (ProofOf proc)) => Processor proc where
    name            :: proc -> String
    instanceName    :: (InstanceOf proc) -> String
    type ProofOf proc                  
    data InstanceOf proc
    solve_          :: SolverM m => InstanceOf proc -> Problem -> m (ProofOf proc)
    solvePartial_   :: SolverM m => InstanceOf proc -> [Rule] -> Problem -> m (PartialProof (ProofOf proc))
    solvePartial_   _ _ prob = return $ PartialInapplicable prob

type ProcessorParser a = CharParser AnyProcessor a 

-- operations

apply :: (SolverM m, Processor proc) => (InstanceOf proc) -> Problem -> m (Proof proc)
apply proc prob = solve proc prob >>= mkProof
    where mkProof = return . Proof proc prob


evalList :: (SolverM m) => Bool -> (a -> Bool) -> [m a] -> m (Either (a,[a]) [a])
evalList True success ms  = do actions <- sequence [ mkIO $ m | m <- ms]
                               liftIO $ pfoldA comb (Right []) actions
    where comb (Right as) a | success a = Continue $ Right $ a : as
                            | otherwise = Stop $ Left (a,as)
          comb (Left _)   _             = error "Processor.evalList: comb called with (Left _) which cannot happen"
evalList False _     []       = return $ Right []
evalList False success (m : ms) = do a <- m
                                     if success a
                                      then do eas <- evalList False success ms
                                              return $ case eas of {Right as -> Right (a:as); Left (f,as) -> Left (f,a:as)}
                                      else return $ Left (a,[])

-- TODO: check for exceptions
evalList' :: (SolverM m) => Bool -> [m a] -> m [a]
evalList' b ms = do Right rs <- evalList b (const True) ms
                    return rs

-- parsable processor

data SynElt = Token String
            | PosArg Int
            | OptArgs

type SynString = [SynElt]

data ArgDescr = ArgDescr { adIsOptional :: Bool
                         , adName       :: String
                         , adDefault    :: Maybe String
                         , adDescr      :: String
                         , adSynopsis   :: String }
              
instance PrettyPrintable ArgDescr where
    pprint d = text "Argument" 
               <+> braces (vcat $ [ attrib "name"         (show $ adName d)
                                  , attrib "isOptional"   (show $ adIsOptional d)
                                  , attrib "description"  (show $ adDescr d)
                                  , attrib "values"       (show $ adSynopsis d)]
                           ++ case adDefault d of 
                                (Just dv) -> [attrib "default" dv]
                                _         -> [])
        where attrib n s = nest 1 $ text n <+> text "=" <+> text s <> text ";"

class Processor a => ParsableProcessor a where
    description     :: a -> [String]
    synString       :: a -> SynString
    posArgs         :: a -> [(Int, ArgDescr)]
    optArgs         :: a -> [ArgDescr]
    parseProcessor_ :: a -> ProcessorParser (InstanceOf a)
    parseFromArgsInteractive :: a -> AnyProcessor -> IO (InstanceOf a)
    -- parseInteractive a procs = pse `liftM` getLine
    --   where pse str = 
    --           case Parse.fromString (parseProcessor a) procs "argument" str of
    --             Right inst -> Just inst
    --             Left _ -> Nothing

mrSynopsis :: ParsableProcessor a => a -> String
mrSynopsis p = unwords $ map f (synString p)
    where f (Token str) = str
          f (PosArg i) = "#" ++ show i
          f (OptArgs)  = "#OPTIONALARGS"

synopsis :: ParsableProcessor a => a -> String
synopsis p = unwords $ deleteAll "" $ map f (synString p)
    where f (Token str) = str
          f (PosArg i) = case lookup i (posArgs p) of 
                           Just d  -> adSynopsis d
                           Nothing -> "<unspecified>"
          f (OptArgs)  = unwords [ "[:" ++ adName d ++ " " ++ adSynopsis d ++ "]"| d <- optArgs p]
          deleteAll _ [] = []
          deleteAll x (y:ys) | x == y    = deleteAll x ys
                             | otherwise = y : deleteAll x ys

parseProcessor :: ParsableProcessor a => a -> ProcessorParser (InstanceOf a)
parseProcessor a =  whiteSpace >> (parens parse Parsec.<|> parse)
    where parse = parseProcessor_ a

fromString :: AnyProcessor -> String -> Either ParseError (InstanceOf SomeProcessor)
fromString p s = mk $ Parse.fromString (parseProcessor p) p "supplied strategy" s
  where mk (Right (OOI inst)) = Right $ SPI $ SomeInstance inst
        mk (Left e)           = Left e
-- * proof

-- ** Answers
data Answer = CertAnswer Certificate 
            | MaybeAnswer
            | YesAnswer
            | NoAnswer
            | TimeoutAnswer deriving (Eq, Ord, Show)

instance Utils.Parsable Answer where
  parse = parseYes Parsec.<|> parseMaybe Parsec.<|> parseTO
    where parseMaybe   = Parsec.string "MAYBE" >> return MaybeAnswer
          parseTO      = Parsec.string "TIMEOUT" >> return TimeoutAnswer
          parseYes     = Utils.parse >>= return . CertAnswer

instance PrettyPrintable Answer where 
  pprint (CertAnswer cert) = pprint cert
  pprint TimeoutAnswer     = text "TIMEOUT"
  pprint MaybeAnswer       = text "MAYBE"
  pprint YesAnswer         = text "YES"
  pprint NoAnswer          = text "NO"

instance ComplexityProof Answer where
    pprintProof a _ = pprint a
    answer = id


answerFromCertificate :: Certificate -> Answer
answerFromCertificate cert = CertAnswer cert

succeeded :: ComplexityProof p => p -> Bool
succeeded p = case answer p of 
                CertAnswer _ -> True
                YesAnswer    -> True
                _            -> False

failed :: ComplexityProof p => p -> Bool
failed = not . succeeded

isTimeout :: ComplexityProof p => p -> Bool
isTimeout p = case answer p of 
                TimeoutAnswer -> True
                _             -> False

certificate :: ComplexityProof p => p -> Certificate
certificate p = case answer p of 
                CertAnswer c -> c
                _            -> uncertified
                
                
--- * Proof Nodes

data Proof proc = Proof { appliedProcessor :: InstanceOf proc
                        , inputProblem     :: Problem 
                        , result           :: ProofOf proc}

instance (Processor proc) => ComplexityProof (Proof proc) where
    pprintProof p@(Proof inst prob res) mde = 
        text "We consider the following Problem:"
        $+$ text ""
        $+$ nest 2 (pprint prob)
        $+$ text ""
        $+$ text "Certificate:" <+> pprint (answer p)
        $+$ text ""
        $+$ case mde of 
              StrategyOutput -> text "Application of" <+> qtext (instanceName inst) <> text ":"
              ProofOutput    -> text "Proof:"
        $+$ nest 2 (pprintProof res mde)
    answer = answer . result

data PartialProof proof = PartialProof { ppInputProblem     :: Problem
                                       , ppResult           :: proof
                                       , ppRemovableDPs     :: [Rule]
                                       , ppRemovableTrs     :: [Rule]
                                       }
                        | PartialInapplicable { ppInputProblem :: Problem }


progressed :: PartialProof proof -> Bool
progressed p = not $ null $ ppRemovableTrs p ++ ppRemovableDPs p

instance (ComplexityProof proof) => ComplexityProof (PartialProof proof) where
  pprintProof p = pprintProof (ppResult p)
  answer p | progressed p = answer $ ppResult p
           | otherwise    = CertAnswer $ certified (constant, constant)

-- * Someprocessor

data SomeProcessor = forall p. (ParsableProcessor p) => SomeProcessor p 
data SomeProof     = forall p. (ComplexityProof p) => SomeProof p
data SomeInstance  = forall p. (Processor p) => SomeInstance (InstanceOf p)

instance ComplexityProof SomeProof where 
    pprintProof (SomeProof p) = pprintProof p
    answer (SomeProof p)      = answer p

instance Typeable (SomeProcessor) where 
    typeOf _ = mkTyConApp (mkTyCon "Tct.Processor.SomeProcessor") [mkTyConApp (mkTyCon "SomeProcessor") []]

instance Typeable (InstanceOf SomeProcessor) where 
    typeOf (SPI _) = mkTyConApp (mkTyCon "Tct.Processor.SPI") [mkTyConApp (mkTyCon "SomeInstance") []]

instance Processor SomeProcessor where
    type ProofOf    SomeProcessor = SomeProof
    data InstanceOf SomeProcessor = SPI SomeInstance
    name (SomeProcessor proc)                    = name proc
    instanceName (SPI (SomeInstance inst))       = instanceName inst
    solve_ (SPI (SomeInstance inst)) prob        = SomeProof `liftM` solve_ inst prob
    solvePartial_ (SPI (SomeInstance inst)) stricts prob = do pp <- solvePartial_ inst stricts prob
                                                              return $ modify pp
        where modify pp = pp { ppResult = SomeProof $ ppResult pp}

instance ParsableProcessor SomeProcessor where
    description     (SomeProcessor proc) = description proc
    synString       (SomeProcessor proc) = synString proc
    posArgs         (SomeProcessor proc) = posArgs proc
    optArgs         (SomeProcessor proc) = optArgs proc
    parseProcessor_ (SomeProcessor proc) = (SPI . SomeInstance) `liftM` parseProcessor_ proc
    parseFromArgsInteractive (SomeProcessor proc) procs = 
      do prs <- parseFromArgsInteractive proc procs
         return $ SPI $ SomeInstance $ prs


instance PrettyPrintable SomeProcessor where
    pprint (SomeProcessor proc) = (ppheading $+$ underline) $$ (nest 2 $ ppdescr $++$ ppsyn $++$ ppargdescr)
        where ppheading = (text "Processor" <+> doubleQuotes (text sname) <> text ":")
              underline = text (take (length $ show ppheading) $ repeat '-')
              ppdescr   | null descr = empty 
                        | otherwise  = vcat [paragraph s | s <- descr]
              ppsyn     = block "Usage" $ text (synopsis proc)
              ppargdescr | length l == 0 = empty
                         | otherwise     = block "Arguments" $ vcat l
                  where l = punctuate (text "" $+$ text "") [hang (text (adName d) <> text ":") 10 (paragraph (adDescr d ++ mshow (adDefault d))) | d <- optArgs proc]
                        mshow Nothing    = "" 
                        mshow (Just def) = " The default is set to '" ++ def ++ "'."
              sname = name proc 
              descr = description proc 
              block n d = text n <> text ":" $+$ nest 1 d

instance Show (InstanceOf SomeProcessor) where 
    show _ = "InstanceOf SomeProcessor"

someProof :: (ComplexityProof p) => p -> SomeProof
someProof = SomeProof

someProofNode :: Processor p => InstanceOf p -> Problem -> ProofOf p -> Proof SomeProcessor
someProofNode proc prob proof = Proof { appliedProcessor = someInstance proc 
                                      , inputProblem = prob
                                      , result = someProof proof}

someProcessorProof :: Processor p => Proof p -> Proof SomeProcessor
someProcessorProof (Proof inst prob proof) = Proof (someInstance inst) prob (someProof proof)

someProcessor :: (ComplexityProof (ProofOf p), ParsableProcessor p) => p -> SomeProcessor
someProcessor = SomeProcessor

someInstance :: forall p. (ComplexityProof (ProofOf p), Processor p) => InstanceOf p -> InstanceOf SomeProcessor
someInstance inst = SPI (SomeInstance inst)

solveBy :: (Processor a, SolverM m) => Problem -> InstanceOf a -> m SomeProof
prob `solveBy` proc = SomeProof `liftM` solve proc prob


-- * Any Processor
-- AnyProcessor a implements a choice of Processors of type a
data AnyProcessor = OO String [SomeProcessor]

instance Processor AnyProcessor where
    type ProofOf AnyProcessor    = SomeProof
    data InstanceOf AnyProcessor = OOI (InstanceOf SomeProcessor)
    name (OO s _)           = s
    instanceName (OOI inst) = instanceName inst
    solve_ (OOI inst) prob  = SomeProof `liftM` solve_ inst prob
    solvePartial_ (OOI inst) stricts prob  = do pp <- solvePartial_ inst stricts prob
                                                return $ modify pp
        where modify pp = pp { ppResult = SomeProof $ ppResult pp}

instance Typeable AnyProcessor where 
    typeOf _ = mkTyConApp (mkTyCon "Tct.Processor.AnyProcessor") [mkTyConApp (mkTyCon "OO") []]

instance Typeable (InstanceOf AnyProcessor) where 
    typeOf _ = mkTyConApp (mkTyCon "Tct.Processor.OOI") [mkTyConApp (mkTyCon "SomeInstance") []]

instance ParsableProcessor AnyProcessor where
    description _             = []
    synString _               = []
    optArgs _                 = []
    posArgs _                 = []
    parseProcessor_ (OO _ []   ) = error "AnyOf.parseProcessor should have at least one processor given"
    -- parseProcessor_ (OO _ (p:ps)) = do inst <- choice [ Parsec.try $ parseProcessor p' | p' <- p:ps]
    --                                    return $ OOI inst
    parseProcessor_ (OO _ ps) = do inst <- choice [ Parsec.try $ parseProcessor p' | p' <- ps]
                                   return $ OOI inst
    parseFromArgsInteractive _ _ = error "AnyOf.parseFromArgsInteractive should not be used"

instance Show AnyProcessor where
    show _ = "AnyProcessor"
instance Show (InstanceOf AnyProcessor) where
    show _ = "InstanceOf AnyProcessor"

infixr 5 <|>
(<|>) :: (ComplexityProof (ProofOf p), ParsableProcessor p) => p -> AnyProcessor -> AnyProcessor
p <|> OO s l = OO s $ someProcessor p : l

infixr 6 <++>
(<++>) :: AnyProcessor -> AnyProcessor -> AnyProcessor
OO s l1 <++> OO _ l2 = OO s $ l1 ++ l2

none :: AnyProcessor
none = OO "any processor" []

toProcessorList :: AnyProcessor -> [SomeProcessor]
toProcessorList (OO _ l) = l

fromProcessorList :: [SomeProcessor] -> AnyProcessor
fromProcessorList l = OO "any processor" l

liftOOI :: InstanceOf SomeProcessor -> InstanceOf AnyProcessor
liftOOI = OOI

parseAnyProcessor :: ProcessorParser (InstanceOf AnyProcessor)
parseAnyProcessor = getState >>= parseProcessor


-- * Construct instances from defaultValues

class IsDefaultOption a where
    defaultOptions :: a
