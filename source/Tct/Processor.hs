{-# OPTIONS_HADDOCK prune #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

----------------------------------------------------------------------------------
-- |
-- Module      :  Tct.Processor
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- License     :  LGPL (see COPYING)
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
--
-- This module defines basic interfaces and functionality concerning
-- complexity processors. A parameterised complexity processor, 
-- a so called /processor instance/, constructs from a complexity problem
-- a proof object. 
----------------------------------------------------------------------------------



module Tct.Processor
    ( -- * Answers
      Answer (..)
    , yesAnswer
      
      -- * Complexity Proofs
    , ComplexityProof (..)      
    , PPMode (..)
    , certificate
    , succeeded
    , failed
    , isTimeout
    , Proof (..)
      -- ** Partial Proofs
    , PartialProof (..)
    , progressed
      
      -- * Complexity Processors
    , Processor (..)
    , apply
    , ParsableProcessor (..)      

    -- * Existentially Quantified Processors, Instances and Proofs
    , SomeProcessor (..)
    , someProcessor
    , SomeInstance (..)
    , someInstance
    , SomeProof (..)
    , someProof
    , someProcessorProof
    , someProofNode
    , solveBy
      
      -- * Any Processor 
    , AnyProcessor
    , toProcessorList
    , fromProcessorList
    , none
    , (<|>)
    , (<++>)
      
      -- * The Solver Monad
    , SolverM (..)
    , SatSolver (..)
    , StdSolverM
    , minisatValue
      
      -- Unexported
    , SolverState (..)
    , ProcessorParser
    , ArgDescr (..)
    , evalList
    , evalList'
    , parseProcessor
    , fromString
    , liftOOI
    , SynElt (..)
    , mrSynopsis
    , haddockComment
    , parseAnyProcessor
    ) 
where

import Control.Monad.Error
import Control.Monad.Reader
import Control.Concurrent.PFold (pfoldA, Return(..))
import Data.Typeable hiding (mkTyCon)

import qualified Qlogic.SatSolver as SatSolver
import Qlogic.SatSolver (Decoder)
import Qlogic.MiniSat (setCmd, MiniSat)
import Text.ParserCombinators.Parsec (CharParser, ParseError, getState, choice)
import qualified Text.ParserCombinators.Parsec as Parsec
import Text.PrettyPrint.HughesPJ hiding (parens)
import Termlib.Problem
import qualified Tct.Utils.Xml as Xml
import Termlib.Utils (PrettyPrintable(..), paragraph, ($++$), qtext)
import qualified Termlib.Utils as Utils
import Termlib.Rule (Rule)
import Tct.Certificate
import qualified Tct.Processor.Parse as Parse

-- | Representation of a SAT-solver. Currently, only 'minisat' (cf. <http://minisat.se>) is supported.
data SatSolver = MiniSat FilePath

-- * The Solver Monad

-- | The interface for a /solver monad/, i.e., the monad under within 
-- an instance of a processor tries to solve the complexity problem.
-- Minimal definition is: 'runSolver', 'mkIO' and 'satSolver'.
class MonadIO m => SolverM m where
  
  -- | some state
  type St m 
  -- | construct an 'IO' monad from a solver monad, when given initial state
  runSolver    :: St m -> m a -> IO a 
  
  -- | construct a 'IO' monad from the given solver monad. This is require
  -- mainly for concurrent execution    
  mkIO         :: m a -> m (IO a) 
  
  -- | return the 'SatSolver'
  satSolver    :: m SatSolver
  
  -- | This method can be used to wrap method 'solve_' from 'Processor'
  solve        :: (Processor proc) => InstanceOf proc -> Problem -> m (ProofOf proc)
  solve = solve_
  
  -- | This method can be used to wrap method 'solvePartial_' from 'Processor'  
  solvePartial :: (Processor proc) => InstanceOf proc -> [Rule] -> Problem -> m (PartialProof (ProofOf proc))
  solvePartial = solvePartial_

-- Basic Solver Monad Implementation

data SolverState = SolverState SatSolver
newtype StdSolverM r = S {runS :: ReaderT SolverState IO r }
    deriving (Monad, MonadIO, MonadReader SolverState)

-- | Standard Implementation for solver monad
instance SolverM StdSolverM where 
    type St StdSolverM = SolverState
    mkIO m            = do s <- ask
                           return $ runSolver s m
    satSolver         = do SolverState s <- ask
                           return s
    runSolver slver m = runReaderT (runS m) slver
                                
minisatValue :: (SolverM m, Decoder e a) => MiniSat () -> e -> m (Maybe e)
minisatValue m e  = 
  do slver <- satSolver
     r <- liftIO $ val slver
     case r of 
       Right v -> return $ Just v
       Left  _ -> return Nothing
    where val (MiniSat s) = SatSolver.value (setCmd s >> m) e 


data PPMode = ProofOutput    -- ^ standard proof output
            | StrategyOutput -- ^ also output of extended /strategy information/
            | OverviewOutput  -- ^ Only present an overview
            deriving (Show, Eq, Ord)

-- | Complexity proofs should be instance of the 'ComplexityProof' class.
class ComplexityProof proof where
    -- | Construct an 'Answer' from the proof.
    answer :: proof -> Answer
    -- | Pretty printer of proof. 
    pprintProof :: proof -> PPMode -> Doc
    
    toXml :: proof -> Xml.XmlContent
    toXml _ = Xml.text "not implemented"
    
-- | A /processor/ 'p' is an object whose /instances/ 'InstanceOf p'
-- are equipped with a /solving method/, translating a complexity 
-- problem into a proof object of type 'ProofOf proc'. 
class (ComplexityProof (ProofOf proc)) => Processor proc where
  -- | The instance of the processor.
  data InstanceOf proc
  -- | The proof type of the processor.
  type ProofOf proc
  -- | Each processor is supposed to have a unique name.
  name            :: proc -> String
  -- | Each instance of the processor should have a name, used in
  -- proof output.
  instanceName    :: (InstanceOf proc) -> String
  
  -- | The solve method. Given an instance and a problem, it constructs
  -- a proof object. This method should not be called directly, instead
  -- the method 'solve' from the class 'SolverM' should be called.
  solve_          :: SolverM m => InstanceOf proc -> Problem -> m (ProofOf proc)
    
  -- | Similar to 'solve_', but constructs a 'PartialProof'. At least all rules
  -- in the additional paramter of type '[Rule]' should be /removed/. Per default, 
  -- this method returns 'PartialInapplicable'. 
  solvePartial_   :: SolverM m => InstanceOf proc -> [Rule] -> Problem -> m (PartialProof (ProofOf proc))
  solvePartial_   _ _ prob = return $ PartialInapplicable prob

type ProcessorParser a = CharParser AnyProcessor a 

-- operations

-- | Similar to 'solve' but wraps the result into a 'Proof' object.
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

-- | Parsable processors provide additional information for parsing.
class Processor a => ParsableProcessor a where
  
    description     :: a -> [String]
    synString       :: a -> SynString
    posArgs         :: a -> [(Int, ArgDescr)]
    optArgs         :: a -> [ArgDescr]
    parseProcessor_ :: a -> ProcessorParser (InstanceOf a)
    parseFromArgsInteractive :: a -> AnyProcessor -> IO (InstanceOf a)

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
parseProcessor a =  Parse.whiteSpace >> (Parse.parens parse Parsec.<|> parse)
    where parse = parseProcessor_ a

fromString :: AnyProcessor -> String -> Either ParseError (InstanceOf SomeProcessor)
fromString p s = mk $ Parse.fromString (parseProcessor p) p "supplied strategy" s
  where mk (Right (OOI inst)) = Right $ SPI $ SomeInstance inst
        mk (Left e)           = Left e
        
-- | The datatype 'Answer' reflects the answer type 
-- from the complexity competition. 
data Answer = CertAnswer Certificate 
            | MaybeAnswer
            | NoAnswer
            | TimeoutAnswer deriving (Eq, Ord, Show)

-- | Abbreviation for 'CertAnswer $ certified (unknown, unknown)'.
yesAnswer :: Answer
yesAnswer = CertAnswer $ certified (unknown, unknown)


instance Utils.Parsable Answer where
  parse = parseYes Parsec.<|> parseMaybe Parsec.<|> parseNo Parsec.<|> parseTO
    where parseMaybe   = Parsec.string "MAYBE" >> return MaybeAnswer
          parseTO      = Parsec.string "TIMEOUT" >> return TimeoutAnswer
          parseNo      = Parsec.string "NO" >> return NoAnswer
          parseYes     = Utils.parse >>= return . CertAnswer

instance PrettyPrintable Answer where 
  pprint (CertAnswer cert) = pprint cert
  pprint TimeoutAnswer     = text "TIMEOUT"
  pprint MaybeAnswer       = text "MAYBE"
  pprint NoAnswer          = text "NO"

instance ComplexityProof Answer where
    pprintProof a _ = pprint a
    answer = id




-- | returns the 'Certificate' associated 
-- with the proof. 
certificate :: ComplexityProof p => p -> Certificate
certificate p = case answer p of 
                CertAnswer c -> c
                _            -> uncertified
                
-- | The predicate @'succeeded' p@ holds iff
-- @'answer' p@ is of shape @CertAnswer _@.
succeeded :: ComplexityProof p => p -> Bool
succeeded p = case answer p of 
                CertAnswer _ -> True
                _            -> False

-- | Negation of 'succeeded'.
failed :: ComplexityProof p => p -> Bool
failed = not . succeeded

-- | The predicate @'isTimeout' p@ holds iff 
-- @'answer' p@ is of shape @TimeoutAnswer _@.
isTimeout :: ComplexityProof p => p -> Bool
isTimeout p = case answer p of 
                TimeoutAnswer -> True
                _             -> False
                
--- * Proof Nodes

-- | Objects of type 'Proof proc' correspond to a proof node, 
-- collecting the applied processor, the input problem and the                
-- proof constructed by the processor                
data Proof proc = Proof { appliedProcessor :: InstanceOf proc
                        , inputProblem     :: Problem 
                        , result           :: ProofOf proc}


instance (Processor proc) => ComplexityProof (Proof proc) where
    pprintProof p@(Proof inst prob res) mde = 
        paragraph ("We are left with following problem, upon which TcT provides the certificate " ++ 
                   (show $ pprint ans) ++ ".")
        $+$ text ""
        $+$ pprintComponents prob
        $+$ text "Obligation:" 
        $+$ nest 2 ppObligation
        $+$ text "Answer:"
        $+$ nest 2 (pprint ans)        
        $+$ text ""
        $+$ case mde of 
              StrategyOutput -> text "Application of" <+> qtext (instanceName inst) <> text ":"
                               $+$ nest 2 (pprintProof res mde)
              OverviewOutput -> text "Overview:"
                               $+$ nest 2 (pprintProof res mde)
              ProofOutput    -> pprintProof res mde
          where ans = answer p
                ppObligation = text strat <> text st
                st = 
                  case startTerms prob of 
                    TermAlgebra {} -> "derivational complexity"
                    BasicTerms {}  -> "runtime complexity"
                strat = 
                  case strategy prob of 
                    Innermost          -> "innermost "
                    Full               -> ""
                    ContextSensitive _ -> "context-sensitive "
                    Outermost          -> "outermost "
    answer = answer . result

-- | Objects of type 'ProofPartial proc' correspond to a proof node
-- obtained by 'solvePartial'. 
data PartialProof proof = PartialProof { ppInputProblem     :: Problem -- ^ The input problem
                                       , ppResult           :: proof -- ^ The proof of the applied processor. @'answer' proof@ 
                                                                    -- must reflect number of applications from rules in 
                                                                    -- 'ppRemovableDPs' and 'ppRemovableTrs' with respect 
                                                                    -- to derivations of the input problem.
                                       , ppRemovableDPs     :: [Rule] -- ^ Dependency pair rules that whose complexity has been 
                                                                     -- estimated by the applied processor.
                                       , ppRemovableTrs     :: [Rule] -- ^ Rules that whose complexity has been 
                                                                     -- estimated by the applied processor.
                                       }
                        | PartialInapplicable { ppInputProblem :: Problem } -- ^ Returned if the processor does not support 
                                                                           -- 'solvePartial'

-- | Returns true iff 'ppRemovableTrs' or 'ppRemovableDPs' is not empty.
progressed :: PartialProof proof -> Bool
progressed p = not $ null $ ppRemovableTrs p ++ ppRemovableDPs p

instance (ComplexityProof proof) => ComplexityProof (PartialProof proof) where
  pprintProof p = pprintProof (ppResult p)
  answer p | progressed p = answer $ ppResult p
           | otherwise    = CertAnswer $ certified (constant, constant)

-- * Someprocessor

-- | Existential quantification of 'ParsableProcessor'. 
data SomeProcessor = forall p. (ParsableProcessor p) => SomeProcessor p 

-- | Existential quantification of 'ComplexityProof'.
data SomeProof     = forall p. (ComplexityProof p) => SomeProof p

-- | Existential quantification of @'Processor' p => 'InstanceOf' p@.
data SomeInstance  = forall p. (Processor p) => SomeInstance (InstanceOf p)

instance ComplexityProof SomeProof where 
    pprintProof (SomeProof p) = pprintProof p
    answer (SomeProof p)      = answer p

instance Typeable (SomeProcessor) where 
    typeOf _ = mkTyConApp (mkTyCon3 "tct" "Tct.Processor" "SomeProcessor") [mkTyConApp (mkTyCon3 "tct" "Tct.Processor"  "SomeProcessor") []]

instance Typeable (InstanceOf SomeProcessor) where 
    typeOf (SPI _) = mkTyConApp (mkTyCon3 "tct" "Tct.Processor" "SPI") [mkTyConApp (mkTyCon3 "tct" "Tct.Processor" "SomeInstance") []]

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

haddockComment :: ParsableProcessor p => p -> Doc
haddockComment proc = 
  Utils.paragraph (escaped $ unlines (description proc))
  $+$ text ""
  $+$ ppargs
    where args = map snd (posArgs proc) ++ optArgs proc
          ppargs | null args = empty
                 | otherwise = vcat [ pparg a $+$ text "" | a <- args]
          pparg a = text "["
                    <> text (adName a) <+> text "::" <+> text (escaped $ adSynopsis  a) 
                    <+> (if adIsOptional a then text "/(optional)/" else empty)
                    <> text "]"
                    <+> text (adDescr a)
          escaped a = concatMap esc $ a
            where esc c | c `elem` "/'`\"@<[]" = ['\\',c]
                        | otherwise            = [c]
                  
                  
  

instance Show (InstanceOf SomeProcessor) where 
    show _ = "InstanceOf SomeProcessor"

-- | Constructor for 'SomeProof'
someProof :: (ComplexityProof p) => p -> SomeProof
someProof = SomeProof

-- | Constructor for a proof node of 'SomeProcessor'
someProofNode :: Processor p => InstanceOf p -> Problem -> ProofOf p -> Proof SomeProcessor
someProofNode proc prob proof = Proof { appliedProcessor = someInstance proc 
                                      , inputProblem = prob
                                      , result = someProof proof}

someProcessorProof :: Processor p => Proof p -> Proof SomeProcessor
someProcessorProof (Proof inst prob proof) = Proof (someInstance inst) prob (someProof proof)

-- | Constructor for 'SomeProcessor'.
someProcessor :: (ComplexityProof (ProofOf p), ParsableProcessor p) => p -> SomeProcessor
someProcessor = SomeProcessor

-- | Constructor for @'InstanceOf' 'SomeProcessor'@.
someInstance :: forall p. (ComplexityProof (ProofOf p), Processor p) => InstanceOf p -> InstanceOf SomeProcessor
someInstance inst = SPI (SomeInstance inst)

-- | Same as 'solve' but wraps the resulting proof into 'SomeProof'.
solveBy :: (Processor a, SolverM m) => Problem -> InstanceOf a -> m SomeProof
prob `solveBy` proc = SomeProof `liftM` solve proc prob


-- * Any Processor
-- | AnyProcessor implements a choice of processors, i.e., a list of processors. 
-- 'AnyProcessor's are mainly used for parsing. The 'InstanceOf' an any procesessor
-- is an instance of one of its elements
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
    typeOf _ = mkTyConApp (mkTyCon3 "tct" "Tct.Processor" "AnyProcessor") [mkTyConApp (mkTyCon3 "tct" "Tct.Processor" "OO") []]

instance Typeable (InstanceOf AnyProcessor) where 
    typeOf _ = mkTyConApp (mkTyCon3 "tct" "Tct.Processor" "OOI") [mkTyConApp (mkTyCon3 "tct" "Tct.Processor" "SomeInstance") []]

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

-- | Add a processor to an 'AnyProcessor'.
(<|>) :: (ComplexityProof (ProofOf p), ParsableProcessor p) => p -> AnyProcessor -> AnyProcessor
p <|> OO s l = OO s $ someProcessor p : l

infixr 6 <++>

-- | Append operation on 'AnyProcessor's.
(<++>) :: AnyProcessor -> AnyProcessor -> AnyProcessor
OO s l1 <++> OO _ l2 = OO s $ l1 ++ l2

-- | The empty 'AnyProcessor'.
none :: AnyProcessor
none = OO "any processor" []

-- | Extract the list of processors from an 'AnyProcessor'.
toProcessorList :: AnyProcessor -> [SomeProcessor]
toProcessorList (OO _ l) = l

-- | Construct an 'AnyProcessor' from a list of processors.
fromProcessorList :: [SomeProcessor] -> AnyProcessor
fromProcessorList l = OO "any processor" l

liftOOI :: InstanceOf SomeProcessor -> InstanceOf AnyProcessor
liftOOI = OOI

-- | 
parseAnyProcessor :: ProcessorParser (InstanceOf AnyProcessor)
parseAnyProcessor = getState >>= parseProcessor


-- * Construct instances from defaultValues

