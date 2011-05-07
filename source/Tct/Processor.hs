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
{-# LANGUAGE UndecidableInstances #-}


--MA:TODO explicit applicable methods => only applicable processors get applied in solve?

module Tct.Processor
    ( SatSolver (..)
    , Processor (..)
    , ParsableProcessor (..)
    , Proof (..)
    , PartialProof (..)
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
    , ComplexityProof
    , Answer (..)
    , Answerable (..)
    , Verifiable (..)
    , VerificationStatus
    , succeeded
    , failed
    , isTimeout
    , certificate
    , answerFromCertificate
    , andVerify
    , allVerify
    , verifyOK
    , verifyFail
    , verifyUnchecked
    , isFail 
    -- * Some Processor
    , SomeProcessor (..)
    , SomeProof (..)
    , SomeInstance (..)
    , someProof
    , someProofNode
    , someProcessor
    , someInstance
    , solveBy
    -- * Any Processor
    , AnyProcessor
    , none
--    , anyOf
    , (<|>)
    , toProcessorList
    , parseAnyProcessor
    -- * Machine Readable Description of Processors
    , SynElt (..)
    , mrSynopsis
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
import qualified Termlib.Utils as Utils
import Termlib.Rule (Rule)
import qualified Termlib.Trs as Trs
import Tct.Certificate
import Tct.Processor.Parse hiding (fromString)
import qualified Tct.Processor.Parse as Parse

data SatSolver = MiniSat FilePath

-- * The Solver Monad

class MonadIO m => SolverM m where
    type St m
    runSolver    :: St m -> m a -> IO a
    mkIO         :: m a -> m (IO a)
    minisatValue :: (Decoder e a) => MiniSat () -> e -> m (Maybe e)
    solve        :: (Processor proc) => InstanceOf proc -> Problem -> m (ProofOf proc)
    solvePartial :: (Processor proc) => InstanceOf proc -> Problem -> m (PartialProof (ProofOf proc))
-- TODO needs to be redone after qlogic-update, allow generic solvers

-- ** Basic Solver Monad Implementation

data SolverState = SolverState SatSolver
newtype StdSolverM r = S {runS :: ReaderT SolverState IO r }
    deriving (Monad, MonadIO, MonadReader SolverState)

instance SolverM StdSolverM where 
    type St StdSolverM = SolverState
    mkIO m            = do s <- ask
                           return $ runSolver s m
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

class (Answerable proof, PrettyPrintable proof, Verifiable proof) => ComplexityProof proof
instance (Answerable proof, PrettyPrintable proof, Verifiable proof) => ComplexityProof proof

class ComplexityProof (ProofOf proc) => Processor proc where
    name            :: proc -> String
    instanceName    :: (InstanceOf proc) -> String
    type ProofOf proc                  
    data InstanceOf proc
    solve_          :: SolverM m => InstanceOf proc -> Problem -> m (ProofOf proc)
    solvePartial_   :: SolverM m => InstanceOf proc -> Problem -> m (PartialProof (ProofOf proc))
    solvePartial_   _ prob = return $ PartialInapplicable prob

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

--- * Answers
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


class Answerable proof where 
    answer :: proof -> Answer

instance Answerable Answer where
    answer = id

answerFromCertificate :: Certificate -> Answer
answerFromCertificate cert = if cert == uncertified
                             then MaybeAnswer
                             else CertAnswer cert

succeeded :: Answerable p => p -> Bool
succeeded p = case answer p of 
                CertAnswer _ -> True
                YesAnswer    -> True
                _            -> False

failed :: Answerable p => p -> Bool
failed = not . succeeded

isTimeout :: Answerable p => p -> Bool
isTimeout p = case answer p of 
                TimeoutAnswer -> True
                _             -> False

certificate :: Answerable p => p -> Certificate
certificate p = case answer p of 
                CertAnswer c -> c
                _            -> uncertified
                
                
--- * Proof Nodes

data Proof proc = Proof { appliedProcessor :: InstanceOf proc
                        , inputProblem     :: Problem 
                        , result           :: ProofOf proc}


instance (Processor proc) => PrettyPrintable (Proof proc) where
    pprint p@(Proof inst prob res) = ppheading $++$ ppres
        where ppheading = (pphead $+$ underline) $+$ ppanswer $+$ ppinput
              pphead    = quotes (text (instanceName inst))
              ppres     = pt "Proof Output" $+$ nest 2 (pprint res)
              ppinput   = pt "Input Problem" <+> measureName prob <+> text "with respect to"
                          $+$ nest 2 (pprint prob)
              ppanswer  = pt "Answer" <+> pprint (answer p)
              underline = text (take (length $ show pphead) $ repeat '-')
              pt s = wtext 17 $ s ++  ":"
              wtext i s = text $ take n $ s ++ repeat ' ' where n = max i (length s)

instance (Answerable (ProofOf proc)) => Answerable (Proof proc) where
    answer p = answer (result p)

instance (Verifiable (ProofOf proc)) => Verifiable (Proof proc) where
    verify prob p = verify prob (result p)

data PartialProof proof = PartialProof { ppInputProblem     :: Problem
                                       , ppResult           :: proof
                                       , ppRemovable        :: [Rule]
                                       }
                        | PartialInapplicable { ppInputProblem :: Problem }

instance (PrettyPrintable proof) => PrettyPrintable (PartialProof proof) where
  pprint p = ppRemoveds
             $+$ text ""
             $+$ text "Details:"
             $+$ nest 2 (pprint (ppResult p))
      where ip = ppInputProblem p
            removeds = ppRemovable p
            ppRemoveds | null removeds = text "No rule was removed:"
                       | otherwise     = text "The following rules were strictly oriented by the relative processor:"
                                         $+$ text ""
                                         $+$ nest 2 (pprint (Trs.fromRules removeds, signature $ ip, variables $ ip))


instance (Answerable proof) => Answerable (PartialProof proof) where
    answer p | length (ppRemovable p) == 0 = CertAnswer $ certified (constant, constant)
             | otherwise = answer $ ppResult p


-- * Someprocessor

data SomeProcessor = forall p. (ParsableProcessor p) => SomeProcessor p 
data SomeProof     = forall p. (ComplexityProof p) => SomeProof p
data SomeInstance  = forall p. (Processor p) => SomeInstance (InstanceOf p)

instance PrettyPrintable SomeProof where pprint (SomeProof p) = pprint p
instance Answerable SomeProof where answer (SomeProof p) = answer p
instance Verifiable SomeProof where verify prob (SomeProof p) = verify prob p

instance Typeable (InstanceOf SomeProcessor) where 
    typeOf (SPI _) = mkTyConApp (mkTyCon "Tct.Processor.SPI") [mkTyConApp (mkTyCon "SomeInstance") []]

instance Processor SomeProcessor where
    type ProofOf    SomeProcessor = SomeProof
    data InstanceOf SomeProcessor = SPI SomeInstance
    name (SomeProcessor proc)                    = name proc
    instanceName (SPI (SomeInstance inst))       = instanceName inst
    solve_ (SPI (SomeInstance inst)) prob        = SomeProof `liftM` solve_ inst prob
    solvePartial_ (SPI (SomeInstance inst)) prob = do pp <- solvePartial_ inst prob
                                                      return $ modify pp
        where modify pp = pp { ppResult = SomeProof $ ppResult pp}

instance ParsableProcessor SomeProcessor where
    description     (SomeProcessor proc) = description proc
    synString       (SomeProcessor proc) = synString proc
    posArgs         (SomeProcessor proc) = posArgs proc
    optArgs         (SomeProcessor proc) = optArgs proc
    parseProcessor_ (SomeProcessor proc) = (SPI . SomeInstance) `liftM` parseProcessor_ proc



instance PrettyPrintable SomeProcessor where
    pprint (SomeProcessor proc) = (ppheading $+$ underline) $$ (nest 2 $ ppsyn $++$ ppdescr $++$ ppargdescr)
        where ppheading = (text "Processor" <+> doubleQuotes (text sname) <> text ":")
              underline = text (take (length $ show ppheading) $ repeat '-')
              ppdescr   = block "Description" $ vcat [paragraph s | s <- descr]
              ppsyn     = block "Usage" $ text (synopsis proc)
              ppargdescr | length l == 0 = empty
                         | otherwise     = block "Arguments" $ vcat l
                  where l = [hang (text (adName d) <> text ":") 10 (paragraph (adDescr d ++ mshow (adDefault d))) $+$ text "" | d <- optArgs proc]
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

someProcessor :: (ComplexityProof (ProofOf p), ParsableProcessor p) => p -> SomeProcessor
someProcessor = SomeProcessor

someInstance :: forall p. (ComplexityProof (ProofOf p), Processor p) => InstanceOf p -> InstanceOf SomeProcessor
someInstance inst = SPI (SomeInstance inst)

solveBy :: (Processor a, SolverM m) => Problem -> InstanceOf a -> m SomeProof
prob `solveBy` proc = SomeProof `liftM` solve proc prob


-- * Any Processor
-- AnyProcessor a implements a choice of Processors of type a
data AnyOf a = OO String [a]
type AnyProcessor = AnyOf SomeProcessor

instance Processor a => Processor (AnyOf a) where
    type ProofOf (AnyOf a)    = SomeProof
    data InstanceOf (AnyOf a) = OOI (InstanceOf a)
    name (OO s _)           = s
    instanceName (OOI inst) = instanceName inst
    solve_ (OOI inst) prob  = SomeProof `liftM` solve_ inst prob
    solvePartial_ (OOI inst) prob  = do pp <- solvePartial_ inst prob
                                        return $ modify pp
        where modify pp = pp { ppResult = SomeProof $ ppResult pp}

instance Typeable (InstanceOf (AnyOf a)) where 
    typeOf (OOI _) = mkTyConApp (mkTyCon "Tct.Processor.OOI") [mkTyConApp (mkTyCon "SomeInstance") []]

instance ParsableProcessor a => ParsableProcessor (AnyOf a) where
    description _             = []
    synString _               = []
    optArgs _                 = []
    posArgs _                 = []
    parseProcessor_ (OO _ ps) = do inst <- choice [ parseProcessor p' | p' <- ps]
                                   return $ OOI inst

instance Show (AnyOf p) where
    show _ = "AnyOf"
instance Show (InstanceOf (AnyOf p)) where
    show _ = "InstanceOf AnyOf"

infixr 5 <|>
(<|>) :: (ComplexityProof (ProofOf p), ParsableProcessor p) => p -> AnyProcessor -> AnyProcessor
p <|> OO s l = OO s $ someProcessor p : l


none :: AnyOf a
none = OO "any processor" []

toProcessorList :: AnyOf p -> [p]
toProcessorList (OO _ l) = l

parseAnyProcessor :: ProcessorParser (InstanceOf AnyProcessor)
parseAnyProcessor = getState >>= parseProcessor


--- * Quasi-verification
                
                
data VerificationStatus = NotChecked | VerificationOK | VerificationFail SomeProof Doc

instance PrettyPrintable VerificationStatus where
  pprint NotChecked = text "Proof not Checked"
  pprint VerificationOK = text "Proof checked"
  pprint (VerificationFail p r) = text ",VERIFICATION' FAILED:"
                                  $+$ r
                                  $+$ pprint p

verifyOK :: VerificationStatus
verifyOK = VerificationOK

verifyUnchecked :: VerificationStatus
verifyUnchecked = NotChecked

verifyFail :: ComplexityProof p => p -> Doc -> VerificationStatus
verifyFail p = VerificationFail (SomeProof p)

class Verifiable proof where 
    verify :: Problem -> proof -> VerificationStatus
    verify _ _ = NotChecked


andVerify :: VerificationStatus -> VerificationStatus -> VerificationStatus
s@(VerificationFail _ _) `andVerify` _                        = s
_                        `andVerify` t@(VerificationFail _ _) = t
s@NotChecked             `andVerify` _                        = s
_                        `andVerify` t@NotChecked             = t
VerificationOK           `andVerify` VerificationOK           = VerificationOK

allVerify :: [VerificationStatus] -> VerificationStatus
allVerify = foldr andVerify VerificationOK

isFail :: VerificationStatus -> Bool
isFail (VerificationFail _ _) = True
isFail _                      = False