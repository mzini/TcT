\documentclass[english]{scrartcl}

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

\usepackage{verbatim}
\newenvironment{code}{\footnotesize\verbatim}{\endverbatim\normalsize}

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

\newcommand{\cde}[1]{\texttt{#1}}
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
whose main function which evaluates the monad \cde{tct config} where \cde{config} 
is used to control the behaviour of \TCT.
In particular, it allows the definition of custom processors that are available 
thru the flag \flag{s} (and of course \flag{l} etc).
This file usually resides in \textsf{\${home}/.tct/}, with either the name \textsf{tct.lhs}
or \textsf{tct.hs}. To start customising \TCT, we import some modules:

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
Further, we import the main function \cde{tct} and the default configuration. 
\begin{code}
import Tct (tct, defaultConfig, Config (..))
\end{code}
\ignore{
\begin{code}
import qualified Tct.Processor as P
\end{code}
}

Finally, we arrive at the \cde{main} function which is defines our resulting \TCT.
Here, we use the default configuration \cde{defaultConfig} but add some 
processors defined in Section~\ref{s:procs}.
\begin{code}
main :: IO ()
main = tct defaultConfig { processors = withMeasure 
                                       <|> processors defaultConfig } 
\end{code}

\section{Defining Processors}\label{s:procs}
\subsection{Processor \cde{withMeasure}}
The first processor we define is the processor \cde{withMeasure}. This 
processor mutates the set of start-terms and the strategy of the given 
problem. This is controlled by a parameter of type \cde{Altering}.
\begin{code}
data Altering = Runtime 
              | Derivational 
              | Innermost 
              | Full 
                deriving (Bounded, Ord, Eq, Show, Typeable, Enum) 
\end{code}
The type \cde{Altering} is a user specified type. The deriving clauses are used to 
make \cde{arg :: Arg (EnumOf Altering)} parsable as [Runtime $\mid$ Derivational $\mid$ Innermost $\mid$ Full].

To define a custom processor, we need to define a (monadic) solving-function.
This function is used to translate problems into proofs.
More precise, such a function takes to arguments: 
(i)  a heterogenous list of \emph{parameters} (constructed by \cde{Unit}, \cde{:+:}), and
(ii) the problem to solve.
It returns a monadic value \cde{m proof} where \cde{m} is a solver monad (c.f. class \cde{Tct.Processor.SolverM})
and \cde{proof} is a complexity proof object, i.e., an instance of the 
class \cde{Tct.Processor.ComplexityProof}.

In our case, the solving-function takes two parameters: 
\cde{alt :: Altering} and \cde{sub :: InstanceOf proc} for \cde{proc} a Processor. 
Here an instance of a processor \cde{proc} is roughtly a \emph{parameterised 
processor}. For instance, the matrix-processor can be parameterised in the dimension. 
Many constructors for such instances are defined in the module \cde{Tct.Methods}.
The function that implements \cde{withMeasure} looks as follows:
\begin{code}
withMeasureSolve :: (P.SolverM m, P.Processor proc) => 
  (Altering :+: P.InstanceOf proc) -> Problem -> m P.SomeProof

withMeasureSolve (alt :+: sub) prob = prob' `solveBy` sub
  where prob' = case alt of 
                  Derivational -> prob { startTerms = TermAlgebra }
                  Innermost    -> prob { strategy = Prob.Innermost }
                  Full         -> prob { strategy = Prob.Full }
                  Runtime      -> prob { startTerms = BasicTerms { defineds = ds
                                                                 , constrs  = cs}}
                    where rs = Prob.strictWeakTrs prob
                          ds = Trs.definedSymbols rs
                          cs = Trs.constructors rs
\end{code}

Here \cde{solveBy} applies a processor to a problem, in our case the problem 
altered according to the parameter \cde{alt}.
To make \cde{withMeasureSolve} into the processor \cde{withMeasure}, we give it a name, 
describe the arguments (the argument-list passed to alterProblem) and give it a description. 
The resulting object can readily be used by \TCT. 

\begin{code}
withMeasure :: CustomProcessor (Arg (EnumOf Altering) :+: Arg Processor) P.SomeProof
withMeasure = customProcessor withMeasureSolve
              Description { as = "withMeasure"
                          , args = arg     { description = "Specifies the property to set"} 
                                   :+: arg { description = "The subprocessor to apply"}
                          , descr = [ "Overwrites set of starting terms respectively"
                                    , "relation before applying the given processor." 
                                    , "UNSOUND depending on usage!"]}

\end{code}
\end{document}