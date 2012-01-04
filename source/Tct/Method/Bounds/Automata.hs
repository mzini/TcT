{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE DeriveDataTypeable #-}

----------------------------------------------------------------------------------
-- |
-- Module      :  Tct.Method.Bounds.Automata
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- License     :  LGPL (see COPYING)
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
--
-- This module implements automata functionality as employed by 
-- the bounds processor.
-----------------------------------------------------------------------------------

module Tct.Method.Bounds.Automata where

import Data.Typeable
import qualified Data.Set as Set
import qualified Data.IntMap as IMap
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.IntMap (IntMap)
import Data.Map (Map)
import Data.Set (Set)
import Control.Monad.State.Class (MonadState(..))
import qualified Control.Monad.State.Lazy as State

import Termlib.Utils (Enumerateable(..), PrettyPrintable(..))
import Termlib.FunctionSymbol (Symbol, Signature)
import Termlib.Term (Term(..))
import Termlib.Trs.PrettyPrint (pprintTrs)

import Text.PrettyPrint.HughesPJ hiding (empty)

-- | This datatype represents the /enrichment/ employed.
data Enrichment = 
  Match -- ^ Matchbounds.
  | Roof -- ^ Roofbounds.
  | Top -- ^ Topbounds.
  deriving (Typeable, Enum, Bounded, Eq)

instance Show Enrichment where
    show Match   = "match"
    show Roof    = "roof"
    show Top     = "top"

data WeakBoundedness = WeakMayExceedBound | WeakMayNotExceedBound

-- TODO:MA: which types should be strict?
type Label = Int
type LSym = (Symbol,Label)
type State = Int

data LTerm = F LSym [LTerm]
           | S State 
    deriving (Eq, Ord)

instance PrettyPrintable LTerm where
    pprint (S s) = pprint s
    pprint (F (f,l) ts) = text (show $ enum f) <> text "_" <> text (show l) <> parens ppts
        where ppts = hcat $ punctuate (text ",") [pprint ti | ti <- ts]
 
instance Show LTerm where
    show = show . pprint

data Rule = Collapse LSym [State] State
          | Epsilon State State deriving (Eq, Ord, Show)


ppRule :: (Symbol -> Doc) -> Rule -> Doc
ppRule _     (Epsilon p q)           = text (show p) <+> text "->" <+> text (show q)
ppRule ppSym (Collapse (f,l) args q) = pplhs <+> text "->" <+> text (show q)
        where pplhs = ppSym f <> text "_" <> text (show l) <> parens ppargs
              ppargs = hsep $ punctuate (text ",") [text (show ai) | ai <- args]

instance PrettyPrintable (Rule, Signature) where
    pprint (r,sig) = ppRule (\ f -> pprint (f,sig)) r

instance PrettyPrintable ([Rule], Signature) where 
    pprint (rules, sig) = pprintTrs (\ r -> pprint (r,sig)) rules

instance PrettyPrintable (Automaton, Signature) where
    pprint (a, sig) = pprint ((toRules a), sig)

instance PrettyPrintable [Rule] where 
    pprint rules = pprintTrs (\ r -> ppRule (text . show) r) rules

instance PrettyPrintable (Automaton) where
    pprint = pprint . toRules

-- TODO:MA: sym -> ... in beiden automaten
type FwdAutomaton = IntMap (IntMap (Map [State] (Set State))) 
-- sym -> l -> args -> qs   <=> forall q \in qs. sym_l(args) -> q \in A

type BwdAutomaton = IntMap (IntMap (IntMap (Set [State])))
-- sym -> q -> l -> argss <=> forall args \in argss. sym_l(args) -> q \in A

data Automaton = Automaton { fwd :: FwdAutomaton
                           , bwd :: BwdAutomaton
                           , fresh :: State
                           , maxlabel :: Label}
                 deriving (Eq, Show)

size :: LTerm -> Int
size (F _ ts) = 1 + sum (map size ts)
size (S _) = 0

isEpsilonRule :: Rule -> Bool
isEpsilonRule (Epsilon _ _) = True
isEpsilonRule (Collapse _ _  _) = False

lift :: Symbol -> Label -> LSym
lift = (,)

base :: LSym -> Symbol
base = fst

height :: LSym -> Label
height = snd

baseTerm :: LTerm -> Term
baseTerm (F f ts) = Fun (base f) $ map baseTerm ts
baseTerm (S _)    = error "Cannot convert a labeled term with Tree automaton states back to a normal term"

toRules :: Automaton -> [Rule]
toRules a = [Collapse (invEnum f,l) args q | (f,m1) <- IMap.toList $ fwd a
                                           , (l,m2) <- IMap.toList m1
                                           , (args, qs) <- Map.toList m2
                                           , q <- Set.toList qs]

fromRules :: [Rule] -> Automaton
fromRules rs = foldl (\ a r -> insert r a) empty rs

empty :: Automaton
empty = Automaton IMap.empty IMap.empty 0 0

freshState :: Automaton -> (State, Automaton)
freshState a = (fr, Automaton (fwd a) (bwd a) (fr  + 1) (maxlabel a))
    where fr = fresh a


freshStates :: Int -> Automaton -> ([State], Automaton)
freshStates 0 a = ([], a)
freshStates i a = case freshStates (i - 1) a' of (qs, a'') -> ((q:qs),a'')
    where (q, a') = freshState a


fwdInsert :: LSym -> [State] -> State -> FwdAutomaton -> FwdAutomaton
fwdInsert (f,l) qs q a = IMap.alter alter1 (enum f) a
        where default3 = Set.singleton q
              default2 = Map.singleton qs default3
              default1 = IMap.singleton l default2
              alter1 = Just . maybe default1 (\ m1 -> IMap.alter alter2 l m1)
              alter2 = Just . maybe default2 (\ m2 -> Map.alter alter3 qs m2)
              alter3 = Just . maybe default3 (\ ps -> Set.insert q ps)


bwdInsert :: LSym -> [State] -> State -> BwdAutomaton -> BwdAutomaton
bwdInsert (f,l) qs q a = IMap.alter alter1 (enum f) a
    where default3 = Set.singleton qs
          default2 = IMap.singleton l default3
          default1 = IMap.singleton q default2
          alter1 = Just . maybe default1 (\ m1 -> IMap.alter alter2 q m1)
          alter2 = Just . maybe default2 (\ m2 -> IMap.alter alter3 l m2)
          alter3 = Just . maybe default3 (\ ps -> Set.insert qs ps)


-- MA:TODO verifizieren dass fresh immer "frisch" ist
insert :: Rule -> Automaton -> Automaton
insert (Collapse sym args q) (Automaton f b fr l) = Automaton (fwdInsert sym args q f) (bwdInsert sym args q b) (maximum $ [fr, q + 1] ++ [a + 1 | a <- args]) (max l $ height sym)
insert (Epsilon p q) (Automaton f b fr l) = Automaton f' b' (maximum [fr, p + 1, q + 1]) l
  where f' = IMap.map (IMap.map $ Map.map addForwardRight) f
        addForwardRight ps = if p `Set.member` ps then Set.insert q ps else ps
        b' = IMap.map addBackwardRight b
        addBackwardRight mp = case IMap.lookup p mp of
                                Just mp' -> addBackwardRight2 mp' mp
                                Nothing  -> mp
        addBackwardRight2 mp' mp = IMap.insertWith addBackwardRight3 q mp' mp
        addBackwardRight3 = IMap.unionWith Set.union
--         f'' = IMap.map (IMap.map addForwardLeft) f'
--         addForwardLeft mp = foldr addForwardLeft2 mp (Map.keys mp)
--         addForwardLeft2 k mp = Set.fold (addForwardLeft3 k) mp (modifiedArgs k)
--         addForwardLeft3 k k' mp = Map.insertWith Set.union k' (fromJust $ Map.lookup k mp) mp
--         b'' = IMap.map (IMap.map $ IMap.map $ Set.unions . Set.toList . Set.map modifiedArgs) b'
--         modifiedArgs []                  = Set.singleton []
--         modifiedArgs (q':qs) | q == q'   = let subresult = modifiedArgs qs in Set.map ((:) p) subresult `Set.union` Set.map ((:) q) subresult
--                              | otherwise = Set.map ((:) q') $ modifiedArgs qs



mkFreshState :: MonadState Automaton m => m State
mkFreshState = do a <- State.get
                  let (qi,a') = freshState a
                  State.put a'
                  return qi

mkInsertRule :: MonadState Automaton m => Rule -> m ()
mkInsertRule r = State.modify (insert r)


step :: Automaton -> LSym -> [State] -> Set State
-- q \in (step A f_l qs) <=> f_l(qs) -> q
step a (f,l) qs = fromMaybe Set.empty look
 where look = do m1 <- IMap.lookup (enum f) (fwd a)
                 m2 <- IMap.lookup l m1
                 Map.lookup qs m2


bstep :: Automaton -> LSym -> State -> Set [State]
-- qs \in bstep f_l q <=> f_l(qs) -> q
bstep a (f,l) q = fromMaybe Set.empty look
    where look = do m1 <- IMap.lookup (enum f) (bwd a)
                    m2 <- IMap.lookup q m1
                    IMap.lookup l m2


bstepUL :: Automaton -> Symbol -> State -> [(Label,Set [State])]
-- (l,[...,qs,...]) \in bstep f q <=> f_l(qs) -> q
bstepUL a f q = fromMaybe [] look
    where look = do m1 <- IMap.lookup (enum f) (bwd a)
                    m2 <- IMap.lookup q m1
                    return $ IMap.toList m2


rulesDefiningUL :: Automaton -> Symbol -> [(Label,[State], Set State)]
-- (l,qs,[...,q,...]) \in rulesDefining f <=> f_l(qs) -> q
rulesDefiningUL a f = fromMaybe [] look
 where look = do m1 <- IMap.lookup (enum f) (fwd a)
                 return [(l,qs,rs) | (l, m2) <- IMap.toList m1
                                   , (qs,rs) <- Map.toList m2]


rulesDefining :: Automaton -> LSym -> [([State], Set State)]
-- (qs,[...,q,...]) \in rulesDefining f_l <=> f_l(qs) -> q
rulesDefining a (f,l) = fromMaybe [] look
 where look = do m1 <- IMap.lookup (enum f) (fwd a)
                 m2 <- IMap.lookup l m1
                 return $ Map.toList m2

symbols :: Automaton -> Set LSym
symbols a = IMap.foldWithKey f Set.empty (fwd a)
    where f fn m s = (Set.fromList [(invEnum fn,l) | l <- IMap.keys m]) `Set.union` s

