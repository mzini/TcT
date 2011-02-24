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

module Main where
import Tct (Config (..), defaultConfig)
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
                                                   (brackets $ vcat [ parens $ text (show i) <+> text "," <+>  pprint d | (i,d) <- positionalArguments d] )
                                    , ppattrib "optionalArguments"
                                      (brackets $ vcat [ pprint d | d <- optionalArguments d] ) ])
          ppattrib n s = nest 1 $ text n <+> text "=" <+> s <> text ";"

main :: IO ()
main = runStrategyInfo defaultConfig