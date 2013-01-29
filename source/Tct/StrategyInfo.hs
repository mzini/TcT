--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.StrategyInfo
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module is used to output processor information in a machine readable
-- way. 
--------------------------------------------------------------------------------   
{-# OPTIONS_HADDOCK hide #-}

module Tct.StrategyInfo where
import Tct (Config (..), processors)
import qualified Tct.Processor as P
import Text.PrettyPrint.HughesPJ
import Termlib.Utils (PrettyPrintable (..))

data Description = Description { name                :: String
                               , description         :: [String]
                               , synopsis            :: String
                               , positionalArguments :: [(Int, P.ArgDescr)]
                               , optionalArguments   :: [P.ArgDescr] 
                               } 


descriptionOf :: P.ParsableProcessor p => p -> Description
descriptionOf p = Description { name                = P.name p
                              , description         = P.description p
                              , synopsis            = P.mrSynopsis p
                              , positionalArguments = P.posArgs p
                              , optionalArguments   = P.optArgs p
                              } 

runStrategyInfo :: Config -> IO ()
runStrategyInfo cfg = putStrLn $ show $ vcat [ pp $ descriptionOf proc | proc <- procs ]
    where procs = P.toProcessorList (processors cfg)
          pp d = text "Strategy" 
                 <+> (braces $ vcat [ ppattrib "name" (text $ name d)
                                    , ppattrib "description" (text (show $ description d))
                                    , ppattrib "synopsis" (text $ show $ synopsis d)
                                    , ppattrib "positionalArguments" 
                                                   (brackets $ vcat [ parens $ text (show i) <+> text "," <+>  pprint a | (i,a) <- positionalArguments d] )
                                    , ppattrib "optionalArguments"
                                      (brackets $ vcat [ pprint a | a <- optionalArguments d] ) ])
          ppattrib n s = nest 1 $ text n <+> text "=" <+> s <> text ";"
