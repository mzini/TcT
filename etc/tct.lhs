\documentclass[english]{scrartcl}
%include polycode.fmt
%format p_1
%format p_2
%format <|> = "\mathrel{\langle\mid\rangle}"
%format >>> = "\ggg"
%format :+: = "\mathrel{{:}{+}{:}}"
\usepackage[utf8x]{inputenc}
\usepackage{xcolor}
\usepackage{listings}
\usepackage{amssymb}
\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{textcomp}
\usepackage{bussproofs}
\usepackage{graphicx}
\usepackage[english]{babel}
\usepackage{tikz}
\usepackage{slashed} 
\usepackage{xargs}
\usepackage[%
numbers, 
sort&compress
]{natbib}   
\usepackage{hyperref}

% \usepackage{verbatim}
% \newenvironment{code}{\footnotesize\verbatim}{\endverbatim\normalsize}

% does not work, why?

% \usepackage{listings}
% \lstloadlanguages{Haskell}
% \lstnewenvironment{code}
%     {\lstset{}%
%       \csname lst@SetFirstLabel\endcsname}
%     {\csname lst@SaveFirstLabel\endcsname}
%     \lstset{
%       basicstyle=\small\ttfamily,
%       flexiblecolumns=false,
%       basewidth={0.5em,0.45em},
%       literate={+}{{$+$}}1 {/}{{$/$}}1 {*}{{$*$}}1 {=}{{$=$}}1
%                {>}{{$>$}}1 {<}{{$<$}}1 {\\}{{$\lambda$}}1
%                {\\\\}{{\char`\\\char`\\}}1
%                {->}{{$\rightarrow$}}2 {>=}{{$\geq$}}2 {<-}{{$\leftarrow$}}2
%                {<=}{{$\leq$}}2 {=>}{{$\Rightarrow$}}2 
%                {\ .}{{$\circ$}}2 {\ .\ }{{$\circ$}}2
%                {>>}{{>>}}2 {>>=}{{>>=}}2
%                {|}{{$\mid$}}1               
%     }

\newcommand{\flag}[1]{\textsf{-#1}}
\newcommand*{\TCT}{\textsf{T\!\raisebox{-1mm}{C}\!T}}
\newcommand{\ignore}[1]{}

\title{\TCT~Configuration Example}

\author{Martin Avanzini and Georg Moser and Andreas Schnabl\\
Institute of Computer Science,\\
University of Innsbruck,\\
Austria
}

\begin{document}

\maketitle

\tableofcontents

\clearpage
\section{Introduction}
 
A \TCT~configuration is a Haskell program (like this literate Haskell file) 
whose main function which evaluates the monad @tct config@ where @config@ 
is used to control the behaviour of \TCT.
In particular, it allows the definition of custom processors that are available 
thru the flag \flag{s} (and of course \flag{l} etc).
This file resides in \textsf{\${home}/.tct/tct.hs}. To start customising \TCT, we import some modules:

\begin{code}
{-# LANGUAGE DeriveDataTypeable, TypeOperators #-}
import Data.Typeable
import Control.Monad (liftM)
import qualified Termlib.Problem as Prob
import Termlib.Problem (StartTerms (..), Problem (..))
import qualified Termlib.Trs as Trs
\end{code}
The following two imports give us access to all predefined techniques from \TCT.
\begin{code}
import Tct.Methods
\end{code}
Further, we import the main function @tct@ and the default configuration. 
\begin{code}
import Tct (tct, defaultConfig, Config (..))
\end{code}
\ignore{
\begin{code}
import Prelude hiding (fail)
import qualified Tct.Processor as P
\end{code}
}

Finally, we arrive at the @main@ function which is defines our resulting \TCT.
Here, we use the default configuration @defaultConfig@ but add some 
processors defined in Section~\ref{s:procs}.
\begin{code}
main :: IO ()
main = tct defaultConfig { processors = withMeasure 
                                       <|> greedyCompose
                                       <|> rcProcessor                                       
                                       <|> processors defaultConfig } 
\end{code}

\section{Defining Processors}\label{s:procs}
\subsection{Processor @withMeasure@}
The first processor we define is the processor @withMeasure@. This 
processor mutates the set of start-terms and the strategy of the given 
problem. This is controlled by a parameter of type @Altering@.
\begin{code}
data Altering = Runtime 
              | Derivational 
              | Innermost 
              | Full 
                deriving (Bounded, Ord, Eq, Show, Typeable, Enum) 
\end{code}
The type @Altering@ is a user specified type. The deriving clauses are used to 
make @arg :: Arg (EnumOf Altering)@ parsable as [Runtime $\mid$ Derivational $\mid$ Innermost $\mid$ Full].

To define a custom processor, we need to define a (monadic) solving-function.
This function is used to translate problems into proofs.
More precise, such a function takes to arguments: 
(i)  a heterogenous list of \emph{parameters} (constructed by @Unit@, @:+:@), and
(ii) the problem to solve.
It returns a monadic value @m proof@ where @m@ is a solver monad (c.f. class @Tct.Processor.SolverM@)
and @proof@ is a complexity proof object, i.e., an instance of the 
class @Tct.Processor.ComplexityProof@.

In our case, the solving-function takes two parameters:
the first one is @alt :: Altering@ and second one is @sub :: InstanceOf proc@ for @proc@ a Processor. 
Here an instance of a processor @proc@ is roughtly a \emph{parameterised 
processor}. For instance, the matrix-processor can be parameterised in the dimension. 
Many constructors for such instances are defined in the module @Tct.Methods@.
The function that implements @withMeasure@ looks as follows:

\begin{code}
withMeasureSolve :: (P.SolverM m, P.Processor proc) => 
  (Altering :+: P.InstanceOf proc) -> Problem -> m P.SomeProof

withMeasureSolve (alt :+: sub) prob = prob' `solveBy` sub where 
  prob'  = case alt of 
             Derivational  ->  prob { startTerms  =  TermAlgebra }
             Innermost     ->  prob { strategy    =  Prob.Innermost }
             Full          ->  prob { strategy    =  Prob.Full }
             Runtime       ->  prob { startTerms  = BasicTerms  {  defineds =  ds
                                                                ,  constrs =  cs}}
  rs     = Prob.allComponents prob
  ds     = Trs.definedSymbols rs
  cs     = Trs.constructors rs
\end{code}

Here @solveBy@ applies a processor to a problem, in our case the problem 
altered according to the parameter @alt@.
To make @withMeasureSolve@ into the processor @withMeasure@, we give it a name, 
describe the arguments (the argument-list passed to alterProblem) and give it a description. 
The resulting object can readily be used by \TCT. 

\begin{code}
withMeasure :: CustomProcessor (Arg (EnumOf Altering) :+: Arg Processor) P.SomeProof
withMeasure = customProcessor withMeasureSolve
              Description {  as     =  "withMeasure"
                          ,  args   =  arg      {  description = "Specifies the property to set"} 
                                       :+: arg  {  description = "The subprocessor to apply"}
                          ,  descr  =  [ "Overwrites set of starting terms respectively"
                                       , "relation before applying the given processor." 
                                       , "UNSOUND depending on usage!"]}
\end{code} 

\subsection{Processor @Greedy Compose@}
\begin{code}

greedyComposeSolve :: (P.SolverM m, P.Processor p_1, P.Processor p_2) => 
  (Maybe Nat :+: Bool :+: P.InstanceOf p_1 :+: P.InstanceOf p_2) 
  -> Problem -> m P.SomeProof

greedyComposeSolve  (Just (Nat 0)  :+:  _            :+:  _        :+:  subproc)  prob  = 
   prob `solveBy` subproc 
greedyComposeSolve  (mn            :+:  useRelative  :+:  relproc  :+:  subproc)  prob  = 
   prob `solveBy` proc where 
        proc   =  composeDynamic useRelative relproc (gc `before` subproc)
        args'  =  mn' :+: useRelative :+: relproc :+: subproc 
           where mn' = (\ n -> n - 1) `fmap` mn
        gc     =  localProcessor "greedycombine (recursive)" (greedyComposeSolve args')


greedyCompose = customProcessor greedyComposeSolve
                Description { as = "greedycompose" 
                            , args = ubound :+: useRel :+: relproc :+: subproc
              , descr = ["This processor applies combine iteratively."]}
            where  ubound   =  (optional (maybeArg naturalArg) "iterations" Nothing) 
                               {description = "Upper bounds on iterations."}
                   useRel   =  (optional boolArg "relative" False)                   
                               {description = "The flag is given to combine" }
                   relproc  =  processorArg 
                               {description = "The processor used to remove rules."}
                   subproc  =  processorArg 
                               {description = "The final processor."}
\end{code}
 
\section{Transformations}
  
\subsection{Simple Accessors}
\begin{code}
wg1     =  weightgap WgOnTrs Algebraic Nothing (nat 1) (Bits 3) (Just (Nat 4)) True
wg3     =  weightgap WgOnTrs Algebraic (Just $ nat 1) (nat 3) (Bits 3) (Just (Nat 4)) True
algebraic_matrix dim = matrix Algebraic Nothing (Nat dim) (Bits 3) (Just (Nat 4)) True
\end{code}
 
\subsection{Some Transformations} 
\begin{code} 
linears =  try wg3
wdg tuples = dependencyPairs tuples >>> try usableRules >>> try pathAnalysis
\end{code}

\subsection{The Processor @rc@} 
\begin{code}
rc tuples   = wdg tuples >>> try linears `thenApply` fastest  [  algebraic_matrix dim 
                                                              |  dim <- [1..3] ]
rcProcessor = processor rc
              Description  { as    =  "rc"
                           , args  =  optional boolArg "tuples" False 
                           , descr =  ["The default RC strategy."]}
\end{code}
\end{document}