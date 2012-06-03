{- | 
Module      :  Tct.Method.Matrix.MatrixInterpretation
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Andreas Schnabl <andreas.schnabl@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

This module defines matrix interpretations.
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

import qualified Tct.Utils.Xml as Xml
import Tct.Encoding.HomomorphicInterpretation
import Tct.Encoding.Matrix
import qualified Tct.Encoding.UsablePositions as UArgs

data MatrixInter a = MI { dimension :: Int
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
                | ConstructorEda (Set.Set F.Symbol) (Maybe Int)
                | EdaMatrix (Maybe Int)
                  deriving Show

toXml :: MatrixInter Int -> MatrixKind -> UArgs.UsablePositions -> [Xml.XmlContent]
toXml mi knd uargs = tpe : [ inter f li | (f,li) <- Map.toList $ interpretations mi ]
  where dim = dimension mi
        sig = signature mi
        tpe = Xml.elt "type" []
               [Xml.elt "matrixInterpretation" [] 
                 [ Xml.elt "domain" [] [Xml.elt "naturals" [] []]
                 , Xml.elt "dimension" [] [Xml.int dim]
                 , Xml.elt "strictDimension" [] [Xml.int (1 :: Int)]
                 , Xml.elt "kind" [] 
                   [ case knd of 
                        UnrestrictedMatrix    -> Xml.elt "unrestricted" [] []
                        ConstructorBased _ mn -> Xml.elt "constructorBased" [] [Xml.int $ maybe dim id mn]
                        TriangularMatrix mn   -> Xml.elt "triangular" [] [Xml.int $ maybe dim id mn]
                        ConstructorEda _ mn   -> Xml.elt "constructorEda" [] [Xml.int $ maybe dim id mn]          
                        EdaMatrix mn          -> Xml.elt "constructorEda" [] [Xml.int $ maybe dim id mn]
                   ]
                 , UArgs.toXml sig uargs]]
        inter f li =
          Xml.elt "interpret" []
           [ Xml.elt "name" [] [Xml.text $ F.symbolName sig f]
           , Xml.elt "arity" [] [Xml.int $ F.arity sig f] 
           , xsum $ 
             (xpoly $ xcoeff $ xvec $ constant li) : 
              [xprod [xpoly $ xcoeff $ xmat m, xvar v ] | (v,m) <- Map.toList $ coefficients li]]
          
        xpoly p = Xml.elt "polynomial" [] [p]
        xsum = xpoly . Xml.elt "sum" []
        xprod = xpoly . Xml.elt "product" []

        xvar (V.Canon i) = xpoly $ Xml.elt "variable" [] [Xml.int i]
        xvar _           = error "non-canonical variable in abstract matrix interpretation"
        
        xcoeff c = Xml.elt "coefficient" [] [c]
        xelt e = xcoeff (Xml.elt "integer" [] [Xml.int e])
        xvec (Vector vs) = Xml.elt "vector" [] [xelt e | e <- vs]
        xmat mx = Xml.elt "matrix" [] [xvec vs | vs <- vvs]
          where (Matrix vvs) = transpose mx

            
instance PropAtom MIVar

instance Functor MatrixInter where
  fmap f mi = MI (dimension mi) (signature mi) $ Map.map (fmap f) (interpretations mi)

instance Functor LInter where
  fmap f li = LI (Map.map (fmap f) (coefficients li)) (fmap f (constant li))

instance (Eq a, PrettyPrintable a, Semiring a) => PrettyPrintable (MatrixInter a) where
  pprint (MI _ sig ints) = vcat $ punctuate (text "" $$ text "") [ p indend | (_, p) <- ps ]
                            
    where ps = [ printInter  f li | (f, li) <- Map.assocs ints]
          printInter f li = (length name, \ ind -> pprintLI name ind ppVar li)
            where name = show $ brackets (pprint (f,sig)) <> ppArgs <+> text "= "
                  ppArgs | null vs = empty
                         | otherwise = parens $ hsep $ punctuate comma [ppVar var | var <- vs]
                  vs = Map.keys $ coefficients $ li
                  ppVar (V.Canon v) = char 'x' <> int v
                  ppVar (V.User v)  = char 'y' <> int v
          indend = maximum (0 : [ len | (len, _) <- ps ])
instance (Eq a, PrettyPrintable a, Semiring a) => PrettyPrintable (LInter a) where
   pprint = pprintLI "" 0 mVar
     where mVar (V.Canon v) = char 'x' <> int v
           mVar (V.User v)  = char 'y' <> int v

instance (Eq a, PrettyPrintable a, Semiring a) => PrettyPrintable (LInter a, V.Variables) where
   pprint (li, var) = pprintLI "" 0 mVar li
     where mVar v = text $ V.variableName v var

pprintLI :: (Eq a, PrettyPrintable a, Semiring a) => String -> Int -> (V.Variable -> Doc) -> LInter a -> Doc
pprintLI name indend ppVar (LI ms vec) = vcat [ text (whenBaseLine i (alignRight indend name))
                                                <> ppRow i | i <- [1..d] ]
    where d = vecdim vec
          vs = [ (var, (show . pprint) `fmap` m) | (var, m) <- Map.toList ms , m  /= zeroMatrix ]
          
          ppRow i = hsep $ 
                    punctuate (text $ whenBaseLine i " +") $
                    [ ppVariableCoefficient i m 
                      <+> text (whenBaseLine i (show (ppVar var))) | (var,m) <- vs] ++ [ppConstant i]
                          
          ppConstant i = brackets $ pprint (vEntry i vec)
          
          ppVariableCoefficient i m = 
            brackets (fsep [ text $ alignRight w cell | (cell, w) <- zip rs widths ])
                                          
            where rs = elts $ row i m
                  widths = [collWidth j | j <- [1..d]]
                  collWidth j = maximum $ 0 : [ length e | e <- elts $ col j m ]
                  

          zeroMatrix = zeromatrix d d
          elts (Vector es) = es          
          
          whenBaseLine :: Int -> String -> String
          whenBaseLine i str 
            | floor mid  == i = str
            | otherwise = [' ' | _ <- str]
              where mid = fromIntegral (d + 1) / (2 :: Rational)
          alignRight pad str = replicate diff ' ' ++ str
            where diff = pad - length str


instance Semiring a => Interpretation (MatrixInter a) (LInter a) where
  interpretFun mi f lis = addAll $ zipWith handleArg [1..] lis
                          where handleArg   = liProd . fmatrix
                                fmatrix i   = find ("coefficient " ++ show (f,i)) (V.Canon i) coeffs
                                finter      = find ("interpretation " ++ show f) f (interpretations mi)
                                coeffs      = coefficients finter
                                addAll      = liBigPlus (constant finter)
                                find e a m = case Map.lookup a m of 
                                                Just r  -> r
                                                Nothing -> error $ "Matrix " ++ e ++ " not found!"
                                  
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

edaMatrix :: RingConst a => MatrixCreate a
edaMatrix f d k = Matrix $ map handlerow [1..d]
                  where handlerow i = Vector $ map (restrictvar . MIVar True f k i) [1..i] ++ map (ringvar . MIVar False f k i) [succ i..d]

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
                                                         EdaMatrix _           -> edaMatrix
                                                         ConstructorEda cs _   -> if f `Set.member` cs
                                                                                  then edaMatrix
                                                                                  else stdMatrix

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
