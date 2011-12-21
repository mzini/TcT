--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Tcti
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, Georg Moser <georg.moser@uibk.ac.at>, 
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module describes the interactive interface to TCT.
-- 
--------------------------------------------------------------------------------      

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


{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
module Tct.Tcti 
    (      
      -- * Loading Problems
      load
      -- | load a problem from the given file
    , loadRC
      -- | same as 'load', overwrites strategy and start-terms 
      -- in order to match a runtime-complexity problem
    , loadIRC
      -- | same as 'load', overwrites strategy and start-terms 
      -- in order to match a innermost runtime-complexity problem
    , loadDC
      -- | same as 'load', overwrites strategy and start-terms 
      -- in order to match a derivational-complexity problem
    , loadIDC      
      -- | same as 'load', overwrites strategy and start-terms 
      -- in order to match a innermost derivational-complexity problem
      
      -- * Inspecting the Current Proof State
    , state
      -- | this procedure prints the current proof state
    , proof
      -- | this procedure prints the current proof tree
    , problems
      -- | returns the list of selected open problems
    , wdgs
      -- | displays the weak dependency graphs of all selected
      -- problems. If 'dot' from the GraphViz project (c.f. <http://www.graphviz.org/>) 
      -- is installed, then a SVG-picture is rendered in 'dg.svg' of
      -- the current working directory
    , cwdgs
      -- | displays the weak congruence dependency graphs of all 
      -- selected problems. To produce an SVG-picture, use the procedure
      -- 'wdgs' that draws weak dependency graphs, but also shows
      -- congruence classes.
    , uargs      
      -- | displays the argument positions of the selected problems

      -- * Modifying the Current Proof State
      -- ** Simplifying and Solving
    , Apply
      -- | instance of the class apply can be used to modify 
      -- the list of (selected) open problems using the procedure 'apply'
    , apply 
      -- | the call 'apply m' applies method 'm' to the list of selected open problems, 
      -- replacing the selected problems with the outcome of applying 'm'. 
      -- For instance, if 'm' is an instance of a processor (see "Tct.Methods#MethodsProcs" for 
      -- a list of processor instances) an the processor succeeds on a 
      -- selected open problem, then this problem is closed.
      -- If 'm' is an instance of a transformation (see "Tct.Methods#MethodsTrans")
      -- that succeeds on an selected open problem, then the this 
      -- problem is replaced by the transformation result.
      -- See also 'describe' for documentation on particular techniques.
      -- 
      -- To change the list of selected problems, see "Tct.Tcti#Select".
      
      -- ** Selecting and Unselecting Problems #Select#      
      -- | Sometimes it is convenient to consider a sublist of the list
      -- of open Problems. To restrict the list of problems considered
      -- by 'apply', use the procedures 'select' and 'unselect', 
      -- in combination with a 'Selector'. 
    , Selector 
      -- | Instances of this class can be used in combination with 
      -- select. Note that Selector 'Int' selects according to the 
      -- problem number as recorded in the state (c.f. procedure 'state').
    , select
      -- | select unsolved problems according to the given 'Selector'
    , unselect
      -- | unselect unsolved problems according to the given 'Selector'        
    , SelectAll
      -- | special selector to select all open problems
    , SelectInv
      -- | special selector to inverse a selection
      
      -- ** Changing the Initial Problem
      -- | The following procedures change the initial problem. 
      -- Note that in order to guarantee soundness, any progress
      -- will undone. However the procedure 'undo' allows to revert 
      -- a change to the initial problem.
    , setRC
      -- | overwrites strategy and start-terms 
      -- in order to match a runtime-complexity problem
    , setIRC
      -- | overwrites strategy and start-terms 
      -- in order to match a innermost runtime-complexity problem
    , setDC
      -- | overwrites strategy and start-terms 
      -- in order to match a derivational-complexity problem
    , setIDC      
      -- | overwrites strategy and start-terms 
      -- in order to match a innermost derivational-complexity problem
      
    , addRuleFromString
      -- | adds the given rule to the input problem. 
      -- Terms are parsed using the simple grammar
      --
      -- - @RULE -> TERM SEP TERM@
      --
      -- - @TERM -> SYM([TERM]*) | SYM@.
      --
      -- Here @SEP@ is either @->@ or @->=@. In the former case, the parsed rule 
      -- is considered a strict rule, in the latter case a weak rule. 
      -- @SYM@ is either the special name @COM@, or any character not matchin @(),\"-=@.
      -- If the root of the left hand side has @^#@ or @#@ as suffix, then 
      -- the rule is considered a dependency pair (these dependency pair suffixes
      -- are stripped off by the parser).
      -- The special symbol @COM@ is replaced by a fresh compound symbol.
    , deleteRuleFromString
      -- | deletes the given rule from the input problem. See 'addRuleFromString'
      -- for grammar
      
      -- ** History Functionality
    , modifyInitialWith      
      -- | modifies the initial problem with using the given function
    , reset
      -- | this procedure resets the proof state to the initially loaded system      
    , undo
      -- | undos the last modification of the proof state
      
      -- * Miscellaneous Functionality
    , help
      -- | displays a help message
    , describe
      -- | opens documentation for the given technique
    , pprint
      -- | pretty-print objects
    , termFromString
      -- | parses a term from a string, with respect
      -- to the signature and variables from the given problem
    , ruleFromString
      -- | parses a rule from a string, with respect
      -- to the signature and variables from the given problem      
    )
where

import Prelude hiding (fail, uncurry)
import qualified Termlib.Problem as Prob
import Termlib.Problem (Problem(..), Strategy(..), StartTerms(..))
import qualified Termlib.Trs as Trs
import Termlib.Term (root,Term)
import Termlib.Rule (Rule(..))
import Termlib.Problem.Parser as ProbParse
import Termlib.Problem.ParseErrors ()
import qualified Termlib.Utils as U
import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Repl as TRepl
import qualified Termlib.Term.Parser as TParser

import Tct.Processor.PPrint
import Tct.Main.Version (version)
import qualified Tct.Processor as P
import qualified Tct.Processor.Transformations as T
import Tct.Method.Combinator (open, OpenProof (..), sequentially, OneOf(..), OneOfProof (..))
import Text.PrettyPrint.HughesPJ
import qualified Tct.Method.DP.DependencyGraph as DG
import qualified Tct.Encoding.UsablePositions as UA

import Data.Maybe (fromMaybe, isJust)
import Data.Typeable (cast)
import Data.List (partition)
import Control.Concurrent (forkIO)
import System.Directory (getCurrentDirectory)
import System.IO.Unsafe
import System.Process (readProcess)
import qualified Control.Exception as Ex
import Data.IORef
import Control.Monad

--------------------------------------------------------------------------------
--- Utils

nb :: String -> Doc          
nb msg = text "NB:" <+> text msg

pprint :: U.PrettyPrintable a => a -> IO ()
pprint a = do putStrLn "" 
              print $ indent $ U.pprint a
              putStrLn ""

bordered :: Doc -> Doc
bordered d = border $$ text "" $$ d $$ text "" $$ border
  where border = text "----------------------------------------------------------------------"

--------------------------------------------------------------------------------
--- Proof Tree
        
data ProofTree = Closed Problem (P.InstanceOf P.SomeProcessor) (P.ProofOf P.SomeProcessor)
               | Transformed Bool Problem (T.TheTransformer T.SomeTrans) (T.ProofOf T.SomeTrans) (Enumeration ProofTree)
               | Open Problem
                 
instance U.PrettyPrintable ProofTree where
  pprint = snd . traverse [1::Int]
    where traverse as (Closed prob proc pproof) = 
            (mans, ppNode as (P.instanceName proc) prob mans detail) 
              where detail = P.pprintProof pproof P.ProofOutput
                    mans   = Just (P.answer pproof)
          
          traverse as (Open prob) = 
            (Nothing, ppNode as "Open Problem" prob Nothing empty)
          
          traverse as pt@(Transformed progressed prob tinst tproof ts) = 
            (mans, ppNode as name prob mans ppProof)
            where ass        = [as ++ [i] | i <- [1..]]
                  ts'        = zip ass [ t | (_,t) <- ts]
                  traverseds = [traverse as' t | (as',t) <- ts']
                  isOpen = not $ all (isJust . fst) traverseds
                  subPPs = [ pp | (_,pp) <- traverseds]
                  name | progressed = T.instanceName tinst
                       | otherwise  = T.instanceName tinst ++ " (without progress)"
                  mans | isOpen    = Nothing
                       | otherwise = Just (P.answer $ proofFromTree pt)
                  ppProof = 
                    T.pprintTProof tinst prob tproof
                    $+$ text ""
                    $+$ ppOverview
                    $+$ ppSubs
                  ppSubs = vcat subPPs
                  ppOverview = 
                    heading "Generated New Problems"
                    $+$ text ""
                    $+$ indent (if null ts'
                                then text "The transformation did not generate new subproblems." 
                                     $+$ text ""
                                else vcat [ text "*" 
                                            <+> ((text "Problem" <+> ppNum as')
                                                 $+$ indent (U.pprint $ problemFromTree t)
                                                 $+$ text "")
                                          | (as',t) <- ts'])

                    
          ppNode :: [Int] -> String -> Problem -> Maybe P.Answer -> Doc -> Doc
          ppNode as name prob manswer detail = 
            heading (show $ ppNum as <+> text name <+> brackets ppAns)
            $+$ text ""
            $+$ indent (ppProb $+$ text "" $+$ detail)
              where ppAns = maybe (text "OPEN") U.pprint manswer
                    ppProb = 
                      text "We consider the following problem:"
                      $+$ indent (U.pprint prob)
          ppNum as = hcat (punctuate (text ".") [text (show a) | a <- as]) <> text ")"
                  
openFromTree :: ProofTree -> Enumeration Problem
openFromTree = openFromTree' (SN (1::Int))
  where openFromTree' _      (Closed _ _ _)           = []
        openFromTree' a      (Open prob)              = [(a,prob)]
        openFromTree' (SN n) (Transformed _ _ _ _ ts) = concatMap (\ (SN m, t) -> openFromTree' (SN (n,m)) t) ts
        
modifyOpenWith :: ProofTree -> (SomeNumbering -> Problem -> ProofTree) -> ProofTree
modifyOpenWith pt f = modifyOpenWith' (SN (1::Int)) pt
  where modifyOpenWith' _      st@Closed{} = st
        modifyOpenWith' a      (Open prob) = f a prob
        modifyOpenWith' (SN n) (Transformed prog prob tinst tproof ts) = 
          Transformed prog prob tinst tproof ts' 
            where ts' = map (\ (SN m, t) -> (SN m, modifyOpenWith' (SN (n,m)) t)) ts

enumOpenFromTree :: ProofTree -> [(Int,(SomeNumbering, Problem))]
enumOpenFromTree tr = zip [1..] (openFromTree tr)


instance Eq SomeNumbering where
  SN a == SN b = Just a == cast b

isUnselected :: ST -> SomeNumbering -> Bool
isUnselected st sn = sn `elem` unselected st

proofFromTree :: ProofTree -> (P.Proof P.SomeProcessor)
proofFromTree (Closed prob proc pproof) = 
  P.Proof { P.appliedProcessor = proc
          , P.result = pproof
          , P.inputProblem = prob}
  
proofFromTree (Open prob) = P.someProofNode open prob OpenProof
proofFromTree (Transformed progressed prob tinst tres subs) = 
  P.someProofNode proc prob tproof
  where 
        subproofs = proofFromTree `mapEnum` subs
        seqProc = sequentially $ [ P.appliedProcessor sub | sub <- toList $ subproofs]
        toSeqProof p = T.liftMS Nothing $ 
                       P.Proof { P.appliedProcessor = seqProc
                               , P.result           = seqProof
                               , P.inputProblem     = P.inputProblem p
                               } 
          where seqProof | P.failed p = OneOfFailed Sequentially [p]
                         | otherwise   = OneOfSucceeded Sequentially p
        proc = tinst `T.thenApply` seqProc                                         
        tproof = 
          T.Proof { T.transformationResult = 
                       case progressed of 
                         True  -> T.Progress tres $ mapEnum P.inputProblem subproofs
                         False -> T.NoProgress tres
                  , T.inputProblem        = prob
                  , T.appliedTransformer  = tinst
                  , T.appliedSubprocessor = T.SSI seqProc
                  , T.subProofs           = toSeqProof `mapEnum` subproofs }
        

problemFromTree :: ProofTree -> Problem 
problemFromTree = P.inputProblem . proofFromTree

--------------------------------------------------------------------------------
--- State

data ST = ST { unselected :: ![SomeNumbering]
             , proofTree  :: Maybe ProofTree}
         

data STATE = STATE { curState :: ST 
                   , hist     :: [ST] 
                   }
                                 
instance U.PrettyPrintable ST where
  pprint st = bordered $ maybe ppEmpty ppTree $ proofTree st
    where ppEmpty = 
            text "No system loaded"
            $+$ text ""
            $+$ nb "Use 'load <filename>' to load a new problem."
          ppTree pt | null opens = 
            text "Hurray, the problem was solved with certicficate" <+> U.pprint (P.answer $ proofFromTree pt)
            $+$ text "Use 'proof' to show the complete proof."
                    | otherwise = 
              block  "Unselected Open Problems" [ (SN i, ppProb prob) | (i,(_,prob)) <- unselecteds]
              $+$ block  "Selected Open Problems"   [ (SN i, ppProb prob) | (i,(_,prob)) <- selecteds]
            where ppProb prob = U.pprint prob
                  opens = enumOpenFromTree pt
                  (unselecteds,selecteds) = partition (\ (_,(sn,_)) -> isUnselected st sn) opens
          
stateRef :: IORef STATE
stateRef = unsafePerformIO $ newIORef (STATE (ST [] Nothing) [])
{-# NOINLINE stateRef #-}

putState :: ST -> IO ()
putState st = do STATE cur hst <- readIORef stateRef 
                 writeIORef stateRef $ (STATE st (cur : hst))

getState :: IO ST
getState = curState `liftM` readIORef stateRef

modifyState :: (ST -> ST) -> IO ()
modifyState f = do st <- getState
                   putState (f st)

load' :: FilePath -> IO ()
load' file = 
  do r <- ProbParse.problemFromFile file
     case r of 
       Left err -> 
         do putStrLn ("Unable to load '" ++ file ++ "'. Reason is:")
            pprint err
            return ()
       Right (prob,warns) -> 
         do ppwarns warns
            modifyState (\ _ -> ST { unselected = []
                                  , proofTree = Just $ Open prob} )
            return ()
  where ppwarns [] = return ()
        ppwarns ws = do putStrLn "Warnings:"
                        pprint `mapM_` ws
                        return ()

undo' :: IO Bool
undo' = 
  do STATE _ hst <- readIORef stateRef 
     case hst of 
       [] -> return False
       (h:hs) -> writeIORef stateRef (STATE h hs) >> return True

resetInitialWith' :: (Problem -> Problem) -> IO ()
resetInitialWith' f = modifyState resetSt
    where resetSt (ST _ Nothing)   = ST [] Nothing
          resetSt (ST _ (Just pt)) = ST [] $ Just $ Open $ f prob
            where prob = problemFromTree pt

printState :: IO ()
printState = do STATE st _ <- readIORef stateRef
                pprint $ st

getProofTree :: IO (Maybe ProofTree)
getProofTree = proofTree `liftM` getState

getOpen' :: IO (Enumeration Problem)
getOpen' = maybe [] openFromTree `liftM` getProofTree


problems' :: IO [Problem]
problems' = 
  do st <- getState
     op <- getOpen'
     return [ p | (sn,p) <- op , not (isUnselected st sn) ]

--------------------------------------------------------------------------------
--- modification of initial problem

setStrategy' :: Strategy -> IO ()
setStrategy' strat = resetInitialWith' (\ prob -> prob { strategy = strat})

setRC' :: IO ()
setRC' = resetInitialWith' f
  where f prob = prob { startTerms = BasicTerms ds cs}
          where rs = Prob.allComponents prob
                ds = Trs.definedSymbols rs
                cs = Trs.constructors rs

setDC' :: IO ()
setDC' = resetInitialWith' f
  where f prob = prob { startTerms = TermAlgebra}

setIRC' :: IO ()
setIRC' = setRC' >> setStrategy' Innermost

setIDC' :: IO ()
setIDC' = setDC' >> setStrategy' Full
        
                                  
addRuleFromString' :: String -> IO ()
addRuleFromString' str = resetInitialWith' $ add . TRepl.parseFromString TParser.rule str

  where add ((True, rl), prob)  | isDP rl prob = prob { strictDPs = strictDPs prob `Trs.union` Trs.singleton rl }
                                | otherwise    = prob { strictTrs = strictTrs prob `Trs.union` Trs.singleton rl }
        add ((False, rl), prob) | isDP rl prob = prob { weakDPs = weakDPs prob `Trs.union` Trs.singleton rl }
                                | otherwise    = prob { weakTrs = weakTrs prob `Trs.union` Trs.singleton rl }
        isDP rl prob' = 
          case root (lhs rl) of 
           Left  _  -> False
           Right f -> F.isMarked (signature prob') f
           
deleteRuleFromString' :: String -> IO ()
deleteRuleFromString' str = resetInitialWith' $ del . TRepl.parseFromString TParser.rule str
  where del ((True, rl), prob)  = prob { strictTrs = strictTrs prob Trs.\\ Trs.singleton rl 
                                       , strictDPs = strictDPs prob Trs.\\ Trs.singleton rl }
        del ((False, rl), prob) = prob { weakTrs = weakTrs prob Trs.\\ Trs.singleton rl 
                                       , weakDPs = weakDPs prob Trs.\\ Trs.singleton rl }

-- --------------------------------------------------------------------------------
-- --- Selection

class Selector i where
  selct :: [(Int, Problem)] -> i -> [Int]

instance Selector Int where  
  selct ep i | any (\ (j,_) -> j == i) ep = [i]
             | otherwise                = []

instance Selector [Int] where  
  selct ep is = concatMap (selct ep) is

data SelectAll = SelectAll

data SelectInv s = SelectInv s 
                   
instance Selector SelectAll where 
  selct ep SelectAll = [i | (i,_) <- ep]
  
instance Selector s => Selector (SelectInv s) where 
  selct ep (SelectInv s) = [i | (i,_) <- ep, not (i `elem` sel) ]
    where sel = selct ep s

instance Selector (Problem -> Bool) where
  selct ep p = [i | (i,prob) <- ep, p prob]


-- ProofTree -> [(Int,(SomeNumbering, Problem))]  
-- enumOpenFromTree

unselect :: Selector sel => sel -> IO ()
unselect sel = modifyState select' >> printState
  where select' st = 
          case proofTree st of 
            Nothing -> st
            Just pt -> st {unselected = [ sn | (i,(sn,_)) <- opens, i `elem` selected ] }
              where selected = selct [(i,prob) | (i,(_,prob)) <- opens ] sel
                    opens = enumOpenFromTree pt

select :: Selector sel => sel -> IO ()
select = unselect . SelectInv


--------------------------------------------------------------------------------
--- Actions 
class Describe a where
  getLocation :: a -> IO (Maybe String)
  
instance T.Transformer t => Describe (T.TheTransformer t) where
  getLocation t = haddockMethod n
    where n = T.name $ T.transformation t

instance P.Processor p => Describe (P.InstanceOf p) where
  getLocation t = haddockMethod n
    where n = P.name $ P.instanceToProcessor t

-- instance P.Processor p => Describe p where
--   getLocation t = haddockMethod n
--     where n = P.name t

describe :: Describe a => a -> IO ()
describe a = openUrl `Ex.catch` handler
  where openUrl =
          do mloc <- getLocation a
             case mloc of 
               Just loc -> 
                 do _ <- forkIO (readProcess "gnome-open" [loc] [] >> return ())
                    return ()
               Nothing -> return ()
        handler (e :: Ex.SomeException) = pprint msg
         where msg = text "Unable to open documentation:"
                     $+$ text (show e)

class Apply a where
  apply' :: a -> Enumeration Problem -> IO (SomeNumbering -> Problem -> Maybe ProofTree)
  
apply :: Apply a => a -> IO ()
apply a = 
  do st <- getState  
     case proofTree st of 
       Nothing -> 
         pprint (text "No system loaded"
                 $+$ text ""
                 $+$ nb "Use 'load <filename>' to load a new problem.")
       Just pt -> applyWithTree st pt
    where applyWithTree st pt = 
            do fn <- apply' a selected
               let fn' sn prob = fromMaybe (Open prob) (fn sn prob)
                   anyChange = any changed [ fn' sn prob | (sn,prob) <- selected]
                   st' = st { proofTree = Just $ pt `modifyOpenWith` fn'}
               pprintResult opens fn
               if anyChange
                then putState st' >> pprint st'
                else pprint (text "No Progress :(")
              where opens = enumOpenFromTree pt
                    selected = [ eprob | (_,eprob@(sn,_)) <- opens, not $ isUnselected st sn]
                    changed Open{}                           = False
                    changed (Closed  _ _ p)                  = P.succeeded p
                    changed (Transformed progressed _ _ _ _) = progressed
 
          pprintResult opens fn = 
            pprint (vcat [ pp i sn prob | (i, (sn,prob)) <- opens ])
              where pp i sn prob = 
                      heading ("Problem " ++ show i)
                      $+$ indent (U.pprint (maybe (Open prob) id (fn sn prob)))
                      -- block' "Considered Problem"
                      -- [ text "We consider the following problem:"
                      --   $+$ indent (U.pprint prob)
                      --   $+$ text ""
                      --   $+$ (case fn sn prob of 
                      --           Nothing  -> text "The problem remains open"
                      --           Just pt' -> U.pprint pt')]

runTct :: P.StdSolverM a -> IO a
runTct = P.runSolver (P.SolverState $ P.MiniSat "minisat2")

instance T.Transformer t => Apply (T.TheTransformer t) where
  apply' t selected = 
    do mrs <- runTct $ evalEnum True [ (i, T.transform tinst prob) | (i, prob) <- selected ]
       case mrs of 
         Nothing -> 
           error "error when transforming some problem"
         Just rs -> 
           return $ \ (SN sn) prob -> mkNode prob `fmap` (find sn rs)
          where mkNode prob res = Transformed progressed prob tinst tproof subTrees
                  where progressed = T.isProgressResult res
                        tproof = T.proofFromResult res
                        subTrees = Open `mapEnum` T.subProblemsFromResult res
      where tinst = T.someTransformation t         
                                      
instance P.Processor p => Apply (P.InstanceOf p) where
  apply' p selected =   
    do mrs <- runTct $ evalEnum False [ (i, P.solve pinst prob) | (i, prob) <- selected ]
       case mrs of 
         Nothing -> error "error when solving some problem"
         Just rs -> return $ \ (SN sn) prob -> mkNode prob `fmap` (find sn rs)
      where mkNode prob res = Closed prob pinst res
            pinst = P.someInstance p
--   apply p = do (ST sel unsel) <- getState
--                let probs = zip (SN `map` [(1::Int)..]) sel
--                
--                  
--                         where Just pps = zipSafe probs rs
--                               printPrfs = pprint $ block "Proofs" [ (SN i, pp prob_i proof_i) | (SN i, (prob_i, proof_i)) <- pps ]
--                                 where pp prob_i proof_i = block' "Considered Problem" [prob_i]
--                                                           $+$ text ""
--                                                           $+$ block' "Processor Output" [P.pprintProof proof_i P.StrategyOutput]

--                               printOverview = pprint $ block "Processor Overview" l
--                                   where l | all (P.failed . snd . snd) pps = enumeration' [text "No Progress :("]
--                                           | otherwise                      = [ (SN i, pp i p_i) | (SN i, (_, p_i )) <- pps ]
--                                         pp _ prf | P.succeeded prf = text "Problem removed." <+> parens (U.pprint $ P.answer prf)
--                                                  | otherwise     = text "Problem unchanged."

--                               setResults = putState (ST newsel unsel)
--                               newsel = concatMap f (toList pps)
--                                   where f (prob_i, proof_i) | P.succeeded proof_i = []
--                                                             | otherwise           = [prob_i]
                                      

  
--------------------------------------------------------------------------------
--- UI
           
haddockPath :: String -> IO (Maybe String)
haddockPath name = fromghcpkg `Ex.catch` (\ (_ :: Ex.SomeException) -> return Nothing)
  where fromghcpkg = process `liftM` readProcess "ghc-pkg" ["describe", name] []
        process ls = msum [ doc (words l) | l <- lines ls]
        doc (d:f:_) 
          | d == "haddock-html:" = Just f
          | otherwise           = Nothing
        doc _ = Nothing

haddockMethod :: String -> IO (Maybe String)
haddockMethod name = do mpt <- haddockPath ("tct-" ++ version) 
                        case mpt of 
                          Nothing -> 
                            do pprint (text "Could not find documentation installed on your system."
                                       $+$ text ""
                                       $+$ nb "Use 'cabal haddock && cabal install' in the source-director of tct to install documentation.")
                               return Nothing
                          Just pt -> 
                            return $ Just $ "file://" ++ pt ++ "/Tct-Methods.html#v:" ++ name

help :: IO ()
help = do haddock <- haddockPath ("tct-" ++ version) 
          tlhaddock <- haddockPath ("termlib")
          let tctidoc = 
                maybe (text "Use 'cabal haddock && cabal install' in the source-directory"
                       $+$ text "of tct to install documentation.")
                (\ p -> text "A list of techniques, and combinators, can be found under:"
                       $+$ indent (text ("file://" ++ p ++ "/Tct-Methods.html"))
                       $+$ text ""
                       $+$ text "Help concerning the interactive mode is available here:"
                       $+$ indent (text ("file://" ++ p ++ "/Tct-Tcti.html"))
                       $+$ text ""
                       $+$ termlibdoc)
                haddock
              termlibdoc = 
                maybe (text "Use 'cabal haddock && cabal install' in the source-directory"
                       $+$ text "of termlib to install documentation of the term rewriting library.")
                (\ p -> text "Documentation of the term rewriting library can be found at:"
                       $+$ indent (text ("file://" ++ p ++ "/Termlib-Repl.html")))
                tlhaddock
          pprint (text "Welcome to TcT-i"
                  $+$ text "----------------"
                  $+$ text ""
                  $+$ text "To start, use 'load \"<filename>\"' in order to to load a problem."
                  $+$ text "Use 'apply t' to simplify the loaded problem using technique 't'."
                  $+$ text "Use 'describe t' to get documentation for 't'."
                  $+$ text ""
                  $+$ tctidoc)

state :: IO ()
state = printState             

reset :: IO ()
reset = resetInitialWith' id >> printState

undo :: IO ()
undo = do undone <- undo' 
          if undone 
            then printState
            else pprint $ text "Nothing to undo"

setRC :: IO ()
setRC = setRC' >> printState

setDC :: IO ()
setDC = setDC >> printState

setIRC :: IO ()
setIRC = setIRC' >> printState

setIDC :: IO ()
setIDC = setIDC' >> printState

load :: FilePath -> IO ()
load fn = load' fn >> printState

loadRC :: FilePath -> IO ()
loadRC n = load' n >> setRC

loadIRC :: FilePath -> IO ()
loadIRC n = load' n >> setIRC

loadDC :: FilePath -> IO ()
loadDC n = load' n >> setDC

loadIDC :: FilePath -> IO ()
loadIDC n = load' n >> setIDC

addRuleFromString :: String -> IO ()
addRuleFromString str = addRuleFromString' str >> printState

deleteRuleFromString :: String -> IO ()
deleteRuleFromString str = deleteRuleFromString' str >> printState

modifyInitialWith :: (Problem -> Problem) -> IO ()
modifyInitialWith f = resetInitialWith' f >> printState

proof :: IO ()  
proof = do st <- getState 
           maybe ppEmpty ppTree $ proofTree st
  where ppEmpty = pprint $ 
          text "No system loaded"
          $+$ text ""
          $+$ nb "Use 'load <filename>' to load a new problem."
        ppTree pt = pprint pt


problems :: IO [Problem]
problems = 
  do ps <- problems'
     mapM_ pprint ps
     return ps
     

wdgs :: IO [DG.DG]   
wdgs = do probs <- problems'
          let dgs = [ (DG.estimatedDependencyGraph DG.Edg prob
                       , Prob.signature prob 
                       , Prob.variables prob) 
                    | prob <- probs ]
          fn <- getCurrentDirectory          
          _ <- forkIO (DG.saveGraphViz dgs "dg.svg" >> return ())
          mapM_ pprint dgs
          putStrLn $ "\nsee also '" ++ fn ++ "/dg.svg'.\n"
          return [dg | (dg,_,_) <- dgs]

cwdgs :: IO [DG.CDG]
cwdgs = problems' >>= mapM f                            
  where f prob = 
          do let dg = DG.toCongruenceGraph $ DG.estimatedDependencyGraph DG.Edg prob
             pprint (dg,Prob.signature prob,Prob.variables prob)
             return dg

uargs :: IO [UA.UsablePositions]
uargs = problems' >>= mapM f
    where f prob = pprint (ua, sig) >> return ua
            where ua = UA.usableArgs (Prob.strategy prob) Trs.empty (Prob.allComponents prob)
                  sig = Prob.signature prob

termFromString :: String -> Problem -> IO (Term, Problem)
termFromString str prob = do pprint term
                             return r
  where r@(term,_) = TRepl.parseFromString TParser.term str prob

ruleFromString :: String -> Problem -> IO (Rule, Problem)
ruleFromString str prob = do pprint rl
                             return (rl,prob')
  where ((_,rl),prob') = TRepl.parseFromString TParser.rule str prob
        
