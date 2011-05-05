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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module Tct.Method.Matrix.MatrixInterpretation 
    -- ( MatrixInter
    -- , MatrixKind(..)
    -- , dimension
    -- , abstractInterpretation
    -- , safeRedpairConstraints
    -- , triConstraints
    -- )
where

import Prelude hiding ((&&),(||),not,any)
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import Data.Foldable (any)
import Data.Typeable
import Text.PrettyPrint.HughesPJ

import Qlogic.Semiring
import Qlogic.Boolean
import Qlogic.PropositionalFormula

import Termlib.Utils
import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Variable as V

import Tct.Encoding.HomomorphicInterpretation
import Tct.Encoding.Matrix


data MatrixInter a = MI {dimension :: Int
                        , signature :: F.Signature
                        , interpretations :: Map.Map F.Symbol (LInter a)}
                        deriving Show
data LInter a = LI {coefficients :: Map.Map V.Variable (Matrix a)
                   , constant :: (Vector a)}
                   deriving Show
data MIVar = MIVar { restrict :: Bool
                   , varfun :: F.Symbol
                   , argpos :: Int
                   , varrow :: Int
                   , varcol :: Int}
                   deriving (Eq, Ord, Show, Typeable)
type MatrixCreate a = F.Symbol -> Int -> Int -> Matrix a

data MatrixKind = UnrestrictedMatrix
                | ConstructorBased (Set.Set F.Symbol) (Maybe Int)
                | TriangularMatrix (Maybe Int)
                | EdaMatrix (Maybe Int)
                  deriving Show

instance PropAtom MIVar

instance Functor MatrixInter where
  fmap f mi = MI (dimension mi) (signature mi) $ Map.map (fmap f) (interpretations mi)

instance Functor LInter where
  fmap f li = LI (Map.map (fmap f) (coefficients li)) (fmap f (constant li))

instance PrettyPrintable a => PrettyPrintable (MatrixInter a) where
  pprint (MI _ sig ints) = (text "Interpretation Functions:" $$ (nest 1 $ printInters ints)) -- (text "Dimension:" <+> int d) $$
    where printInters = vcat . map (uncurry printInter) . Map.assocs
          printInter f li = fHead <+> nest (length (show fHead) + 1) (pprint li)
            where fHead = pprint (f,sig) <> fargs li <+> char '='
                  fargs = parens . hsep . punctuate comma . map (\(V.Canon i) -> char 'x' <> int i) . Map.keys . coefficients

instance PrettyPrintable a => PrettyPrintable (LInter a) where
   pprint = pprintLI mVar
     where mVar (V.Canon v) = char 'x' <> int v
           mVar (V.User v)  = char 'y' <> int v
--   pprint (LI ms vec) = foldr handleLine empty [1..d]
--     where handleLine i doc               = Map.foldWithKey (handleMatrix i) (vLine i) ms $$ doc
--           handleMatrix i v m doc         = mLine i m <+> mVar i v <+> doc
--           colWidths m                    = map (\j -> (maximum . liftVector (map prettyLength) . col j) m) [1..d]
--           mLine i m                      = brackets $ foldr mCell empty (liftVector (`zip` (colWidths m)) (row i m))
--           mCell (cell, l) doc            = text (replicate (l - prettyLength cell) ' ') <> pprint cell <+> doc
--           mVar i (V.Canon v) | i == 1    = char 'x' <> int v <+> char '+'
--           mVar _ (V.Canon v) | otherwise = text $ replicate (length (show v) + 3) ' '
--           mVar i (V.User v)  | i == 1    = char 'y' <> int v <+> char '+'
--           mVar _ (V.User v)  | otherwise = text $ replicate (length (show v) + 3) ' '
--           vLine i                        = brackets $ pprint (vEntry i vec)
--           prettyLength                   = length . show . pprint
--           d                              = vecdim vec

instance PrettyPrintable a => PrettyPrintable (LInter a, V.Variables) where
   pprint (li, var) = pprintLI mVar li
     where mVar v = text $ V.variableName v var

pprintLI :: PrettyPrintable a => (V.Variable -> Doc) -> LInter a -> Doc
pprintLI f (LI ms vec) = foldr handleLine empty [1..d]
    where handleLine i doc       = Map.foldrWithKey (handleMatrix i) (vLine i) ms $$ doc
          handleMatrix i v m doc = mLine i m <+> mVar i v <+> doc
          colWidths m            = map (\j -> (maximum . liftVector (map prettyLength) . col j) m) [1..d]
          mLine i m              = brackets $ foldr mCell empty (liftVector (`zip` (colWidths m)) (row i m))
          mCell (cell, l) doc    = text (replicate (l - prettyLength cell) ' ') <> pprint cell <+> doc
          mVar i v | i == 1      = f v <+> char '+'
          mVar _ v | otherwise   = text $ replicate (length (show $ f v) + 2) ' '
          vLine i                = brackets $ pprint (vEntry i vec)
          prettyLength           = length . show . pprint
          d                      = vecdim vec

-- pprint' :: PrettyPrintable a => LInter a -> Doc
-- pprint' (LI ms v) = Map.foldWithKey pArg (pVector v) ms
--     where pArg (V.Canon i) m doc  = pMatrix m <> char 'x' <> int i <+> char '+' <+> doc
--           pArg (V.User i) m doc   = pMatrix m <> char 'y' <> int i <+> char '+' <+> doc
--           pVector                 = vcat . liftVector (map (brackets . pprint))
--           pMatrix (Matrix m)      = (vcat (map (const lbrack) m)) <> pMatrix' m <> vcat (map (const rbrack) m)
--           pMatrix' m | any (liftVector null) m = empty
--           pMatrix' m | otherwise               = (vcat (map (liftVector (pprint . head)) m)) <+>
--                                                    pMatrix' (map (liftVector_ tail) m)

instance Semiring a => Interpretation (MatrixInter a) (LInter a) where
  interpretFun mi f lis = addAll $ zipWith handleArg [1..] lis
                          where handleArg   = liProd . fmatrix
                                fmatrix i   = Maybe.fromJust $ Map.lookup (V.Canon i) (coefficients finter)
                                finter      = Maybe.fromJust $ Map.lookup f $ interpretations mi
                                addAll      = liBigPlus (constant finter)
  interpretVar mi v     = LI (Map.singleton v (unit dim)) (zerovec dim)
                          where dim = dimension mi

stdMatrix :: RingConst a => MatrixCreate a
stdMatrix f d k = Matrix $ map handlerow ds
                  where handlerow i = Vector $ map (ringvar . MIVar False f k i) ds
                        ds          = [1..d]

triMatrix :: RingConst a => MatrixCreate a
triMatrix f d k = Matrix $ map handlerow [1..d]
                  where handlerow i = Vector $ replicate (pred i) czero ++ (midvar i : map (ringvar . MIVar False f k i) [succ i..d])
                        midvar i = restrictvar $ MIVar True f k i i

abstractInterpretation :: RingConst a => MatrixKind -> Int -> F.Signature -> MatrixInter a
abstractInterpretation mk d sig = (MI d sig . Map.fromList . map (\f -> (f, interpretf f)) . Set.elems . F.symbols) sig
                                  where interpretf f = LI (fcoeffs f) (fconst f)
                                        fcoeffs f    = Map.fromList (map (\x -> (V.Canon x, (op f) f d x)) [1..F.arity sig f])
                                        fconst f     = Vector $ map (ringvar . (\x -> MIVar False f 0 x 0)) [1..d]
                                        op f         = case mk of
                                                         UnrestrictedMatrix    -> stdMatrix
                                                         TriangularMatrix _    -> triMatrix
                                                         ConstructorBased cs _ -> if f `Set.member` cs
                                                                                  then triMatrix
                                                                                  else stdMatrix
                                                         EdaMatrix _           -> stdMatrix

liProd :: Semiring a => Matrix a -> LInter a -> LInter a
liProd m li = LI (Map.map (mprod m) (coefficients li)) (mvprod m (constant li))

liBigPlus :: Semiring a => Vector a -> [LInter a] -> LInter a
liBigPlus v lis = LI coeffs (bigvplus $ v : (map constant lis))
                  where coeffs = Map.unionsWith mplus $ map coefficients lis

triConstraints :: AbstrOrdSemiring a b => MatrixInter a -> b
triConstraints = bigAnd . Map.map (bigAnd . Map.map triConstraint . coefficients) . interpretations
                 where triConstraint m = bigAnd $ map (\i -> entry i i m .<=. one) [1..(dim m)]
                       dim             = uncurry min . mdim

maxNonIdMatrix :: (AbstrOrdSemiring a Bool, AbstrEq (Matrix a) Bool) => MatrixInter a -> Matrix a
maxNonIdMatrix mi = if any (any (.==. unit d) . coefficients) (interpretations mi) && maxi .==. zeromatrix d d then unit 1 else maxi
  where maxi = maximumMatrix (d, d) $ Map.map (maximumMatrix (d, d) . Map.filter (./=. (unit d)) . coefficients) $ interpretations mi
        d    = dimension mi

maxMatrix :: AbstrOrdSemiring a Bool => MatrixInter a -> Matrix a
maxMatrix mi = maximumMatrix (d, d) $ Map.map (maximumMatrix (d, d) . coefficients) $ interpretations mi
  where d  = dimension mi
