{-# LANGUAGE FlexibleInstances #-}
module Tct.Tcti 
    (
     load
    , apply 
    , state
    , initialProblem
    , reset
    , undo 
    , get
    , select
    , unselect
    , selectAll
    , unselectAll
    , selectInverse
    , filterSelect
    , setRC
    , setDC
    , setStrategy
    , help
    , pprint
    )
where

import Prelude hiding (fail, uncurry)
import Termlib.Problem as Prob
import Termlib.Trs as Trs
import Termlib.Problem.Parser as ProbParse
import Termlib.Problem.ParseErrors ()
import qualified Termlib.Utils as U

import Tct.Processor.PPrint
import qualified Tct.Processor as P
import qualified Tct.Processor.Transformations as T
import Text.PrettyPrint.HughesPJ hiding (empty)

import Data.Maybe (fromMaybe)
import Data.List
import System.IO.Unsafe
import Data.IORef
import Control.Monad

--------------------------------------------------------------------------------
--- Utils

nb :: String -> Doc          
nb msg = text "  NB:" <+> text msg

pprint :: U.PrettyPrintable a => a -> IO ()
pprint a = do putStrLn "" 
              print $ indent $ U.pprint a
              putStrLn ""

bordered :: Doc -> Doc
bordered d = border $$ text "" $$ d $$ text "" $$ border
  where border = text "----------------------------------------------------------------------"

--------------------------------------------------------------------------------
--- State

data ST = ST { selected   :: ![Problem]
             , unselected :: ![Problem] }
         
data STATE = STATE { curState :: ST 
                   , hist     :: [ST] 
                   , loaded  :: Maybe Problem}
          
          
stateRef :: IORef STATE
stateRef = unsafePerformIO $ newIORef (STATE (ST [] []) [] Nothing)
{-# NOINLINE stateRef #-}

getState :: IO ST
getState = curState `liftM` readIORef stateRef

get :: Int -> IO Problem
get i = do st <- getState
           let l = selected st ++ unselected st
           if 1 <= i && i <= length l 
            then return $ l!!(i - 1)
            else error "Index out of bound"

initialProblem :: IO Problem
initialProblem = fromMaybe (error "No problem loaded") `liftM` loaded `liftM` readIORef stateRef

putState :: ST -> IO ()
putState st = do STATE cur hst mprob <- readIORef stateRef 
                 writeIORef stateRef $ (STATE st (cur : hst) mprob)

printState :: IO ()
printState = do STATE st _ _ <- readIORef stateRef
                pprint $ st

modifyState :: (ST -> ST) -> IO ()
modifyState f = do st <- getState
                   putState (f st)

reset :: IO ()
reset = do STATE _ _ mprob <- readIORef stateRef 
           case mprob of 
             Just prob -> writeIORef stateRef (STATE (ST [prob] []) [] mprob) >> printState
             Nothing   -> writeIORef stateRef (STATE (ST [] []) [] Nothing) >> printState
           
undo :: IO ()
undo = do STATE _ hst mprob <- readIORef stateRef 
          case hst of 
            [] -> error "Nothing to undo"
            (h:hs) -> writeIORef stateRef (STATE h hs mprob) >> printState
                      

load :: FilePath -> IO ()
load file = do r <- ProbParse.problemFromFile file
               case r of 
                 Left err -> do putStrLn ("Unable to load '" ++ file ++ "'. Reason is:")
                                pprint err
                                return ()
                 Right (prob,warns) -> do ppwarns warns
                                          writeIORef stateRef (STATE (ST [prob] []) [] (Just prob))
                                          printState
                                          return ()
  where ppwarns [] = return ()
        ppwarns ws = do putStrLn "Warnings:"
                        pprint `mapM_` ws
                        return ()
--        pprob prob = hang (text "Following problem loaded:") 2 (U.pprint prob) 


instance U.PrettyPrintable ST where
  pprint st = bordered $ block' "Proof State" (pprint' st)
    where pprint' (ST [] [])     = [text "Empty"
                                    $$ text ""
                                    $$ nb "Use 'load <filename>' to load a new problem."
                                    $$ text""]
          pprint' (ST sel [])    = [ block "Selected Problems" (pp 1 sel)]
          pprint' (ST [] usel)   = [ block "Unselected Problems" (pp 1 usel)]
          pprint' (ST sel usel)  = [ block "Selected Problems" (pp 1 sel)
                                   , block "Unselected Problems" (pp (length sel + 1) usel)]
          pp j l = [ (SN i, U.pprint p $$ text "") | (i,p) <- zip [(j::Int)..] l]


--------------------------------------------------------------------------------
--- Selection

data CSelector = Inv
               | All

class Selector i where
  selct :: i -> (ST -> ST)
  
instance Selector Int where  
  selct i st@(ST sel unsel) | 0 < i' && i' <= length unsel  = ST (unsel!!(i'-1) : sel) (drp i' unsel)
                            | otherwise                   = st
     where i' = i - length sel
           drp _ []     = []
           drp 1 (_:xs) = xs
           drp n (x:xs) = x : drp (n - 1) xs

instance Selector CSelector where 
  selct Inv st = flipSelected st
  selct All (ST sel unsel) = ST (sel ++ unsel) []
  
instance Selector [Int] where  
  selct = flip $ foldl (flip selct)

instance Selector (Problem -> Bool) where
  selct f (ST sel unsel) = (ST yes no)
    where (yes,no) = partition f (sel ++ unsel)

flipSelected :: ST -> ST
flipSelected (ST a b) = ST b a

applySelect :: Selector i => Bool -> i -> IO ()
applySelect unsel i = modifyState (flp . selct i . flp) >> printState
  where flp | unsel = flipSelected
            | otherwise = id

select :: Int -> IO ()
select = applySelect False

unselect :: Int -> IO ()
unselect = applySelect True

selectAll :: IO ()
selectAll = applySelect False All

unselectAll :: IO ()
unselectAll = applySelect True All

selectInverse :: IO ()
selectInverse = applySelect False Inv

filterSelect :: (Problem -> Bool) -> IO ()
filterSelect = applySelect False


runTctSolver :: P.StdSolverM a -> IO a
runTctSolver = P.runSolver (P.SolverState $ P.MiniSat "minisat2")


modify :: (Problem -> Problem) -> IO ()
modify f = modifyState (\ st -> st { selected = f `map` selected st})

setStrategy :: Strategy -> IO ()
setStrategy strat = modify (\ prob -> prob { strategy = strat})

setRC :: IO ()
setRC = modify f >> printState
  where f prob = prob { startTerms = BasicTerms ds cs}
          where rs = allComponents prob
                ds = definedSymbols rs
                cs = constructors rs

setDC :: IO ()
setDC = modify f  >> printState
  where f prob = prob { startTerms = TermAlgebra}

state :: IO ()
state = printState 


help :: IO ()
help = pprint $ block' "Commands" [U.columns 2 (transpose rows)]
  where rows = map mk [ ("load :: FilePath -> IO ()", "Loads a problem from given file") 
                      , ("apply :: Applies a => a -> IO ()", "applies 'a' to the selected problems. Currently transformations, processors and functions 'f :: Problem -> Problem' can be applied to the proof state.")
                      , ("get :: Int -> IO ()", "get the i-th problem from the state")                         
                      , epty                        
                      , ("state :: IO ()", "displays the current state")                                                 
                      , ("reset :: IO ()", "reset the proof state and history") 
                      , ("undo :: IO ()", "undo last proof state modification") 
                      , epty
                      , ("select :: Int -> IO ()", "adds the i-th problem to set of selected problems")
                      , ("unselect :: Int -> IO ()", "removes the i-th problem from the set of selected problems")
                      , ("selectAll :: IO ()", "selects all problems to process") 
                      , ("unselectAll :: IO ()", "unselects all problems to process")                         
                      , ("selectInverse :: IO ()", "inverses problem selection")                         
                      , ("filterSelect :: (Problem -> Bool) -> IO ()", "selects all those problems that satisfy the given predicate")
                      , epty                                                
                      , ("setRC :: IO ()", "sets all selected problems to RC problems")
                      , ("setDC :: IO ()", "sets all selected problems to DC problems")
                      , ("setStrategy :: Strategy -> IO ()", "sets strategy of all selected problems")
                      , epty                                                
                      , ("help :: IO ()", "this message")
                      ]
        mk (a,c) = [indent $ text a, U.paragraph c]
        epty = ("","")


--------------------------------------------------------------------------------
--- Actions 

class Apply a where
  apply :: a -> IO ()
  

instance T.Transformer t => Apply (T.TheTransformer t) where
  apply t =   do (ST sel unsel) <- getState
                 let probs = zip (SN `map` [(1::Int)..]) sel
                 mrs <- runTctSolver $ evalEnum True [ (i, T.transform t prob) | (i, prob) <- probs ]
                 case mrs of 
                   Nothing -> error "error when transforming some problem"
                   Just rs -> do {printResults; printOverview; setResults; putStrLn "";  }
                      where Just probResEnum = zipSafe probs rs
                            progressedResults = [(i, res) | (i, (_,res)) <- probResEnum, isProgress res ]
                            printResults = pprint $ block "Transformation Results" [ (SN i, pp i prob_i res_i) | (SN i, (prob_i, res_i)) <- probResEnum ]
                              where pp i prob_i res_i = block' "Considered Problem" [prob_i]
                                                        $+$ text ""
                                                        $+$ ppres
                                      where ppres = case res_i of 
                                              T.Progress p_i subprobs_i -> block' "Transformation Output (progress)" [T.pprintProof t prob_i p_i]
                                                                           $+$ text ""
                                                                           $+$ block "Computed new problem(s)" [ (SN (i,j), prob_ij) | (SN j, prob_ij) <- subprobs_i ]
                                              T.NoProgress p_i -> block' "Transformation Output (no progress)" [T.pprintProof t prob_i p_i]                                              
                            printOverview = pprint $ block "Transformation Overview" l
                                where l | null progressedResults = enumeration' [text "No Progress :("]
                                        | otherwise              = [ (SN i, pp i res_i) | (SN i, (_, res_i )) <- probResEnum ]
                                      pp _ (T.Progress _ ps) = text "Problem split into" <+> text (show $ length ps)  <+> text "new problem(s)."
                                      pp _ (T.NoProgress _) = text "Problem unchanged."
                            isProgress (T.Progress _ _) = True
                            isProgress (T.NoProgress _) = False
                            setResults = putState (ST newsel unsel)
                            newsel = concatMap f (toList probResEnum)
                                where f (_     , T.Progress _ ps) = toList ps
                                      f (prob_i, T.NoProgress _)  = [prob_i]
                                      
instance P.Processor p => Apply (P.InstanceOf p) where
  apply p = do (ST sel unsel) <- getState
               let probs = zip (SN `map` [(1::Int)..]) sel
               mrs <- runTctSolver $ evalEnum False [ (i, P.solve p prob) | (i, prob) <- probs ]
               case mrs of 
                 Nothing -> error "error when solving some problem"
                 Just rs -> do {printPrfs; printOverview; setResults; }
                        where Just pps = zipSafe probs rs
                              printPrfs = pprint $ block "Proofs" [ (SN i, pp prob_i proof_i) | (SN i, (prob_i, proof_i)) <- pps ]
                                where pp prob_i proof_i = block' "Considered Problem" [prob_i]
                                                          $+$ text ""
                                                          $+$ block' "Processor Output" [U.pprint proof_i]

                              printOverview = pprint $ block "Processor Overview" l
                                  where l | all (P.failed . snd . snd) pps = enumeration' [text "No Progress :("]
                                          | otherwise                      = [ (SN i, pp i p_i) | (SN i, (_, p_i )) <- pps ]
                                        pp _ prf | P.succeeded prf = text "Problem removed." <+> parens (U.pprint $ P.answer prf)
                                                 | otherwise     = text "Problem unchanged."

                              setResults = putState (ST newsel unsel)
                              newsel = concatMap f (toList pps)
                                  where f (prob_i, proof_i) | P.succeeded proof_i = []
                                                            | otherwise           = [prob_i]
                                      

instance Apply (Problem -> Problem) where 
   apply = modify
                
