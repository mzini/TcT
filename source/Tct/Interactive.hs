{- | 
Module      :  Tct.Interactive
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
License     :  LGPL (see COPYING)

Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

This section describes the /interactive interface/ of TcT (/TcT-i/ for short), 
for usage information on the /command line interface/, please 
refer to "Tct". 
Since TcT-i relies on the Interpreter 'ghci' from the Glasgow 
Haskell Compiler (<http://www.haskell.org/ghc/>), the interactive
interface is only available if 'ghci' is present on your system.
As explained in "Tct.Configuration", 
TcT can be easily customized. TcT-i makes use of this by loading 
the configuration file, usually located in @${HOME}\/.tct\/tct.hs@.

The interactive interface is invoked from the command line as follows:

>>> tct -i
GHCi, version 7.0.3: http://www.haskell.org/ghc/  :? for help
...
Loading package tct-1.9 ... linking ... done.
[1 of 1] Compiling Main             ( tct.hs, interpreted )
Ok, modules loaded: Main.
.
  Welcome to the TcT
  ------------------
.  
  This is version 1.8 of the Tyrolean Complexity Tool.
.  
  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>,
      Georg Moser <georg.moser@uibk.ac.at>, and
      Andreas Schnabl <andreas.schnabl@uibk.ac.at>.
.  
  This software is licensed under the GNU Lesser General Public
  License, see <http://www.gnu.org/licenses/>.
.  
  Don't know how to start? Type 'help'.
TcT> 

As can be readily seen from the output,  
this command starts a customized version of 'ghci'. 
In particular all the functionality of 'ghci' is available, cf.
<http://www.haskell.org/ghc/docs/latest/html/users_guide/ghci.html>
on general usage information of 'ghci'.

-}

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
module Tct.Interactive
    (      
      -- * Loading Problems
      -- | A complexity problem can be loaded into TcT-i by invoking
      -- the 'load' action. This action accepts a file path refering  
      -- to either a file in the old tpdb-format (cf. <http://www.lri.fr/~marche/tpdb/format.html>)
      -- or in the new xml-based format (cf. <http://dev.aspsimon.org/xtc.xsd>).
      -- Examples are available in the directory 'examples' in the software distribution, 
      -- or the current termination problem database 
      -- (<http://termcomp.uibk.ac.at/status/downloads/tpdb-current-exported.tar.gz>).
      load
      -- | Loads a complexity problem from the given file.
      -- 
      -- >>> load "examples/quot.trs" 
      -- --------------------------------------------------------------------
      -- Selected Open Problems:
      -- -----------------------
      -- Strict Trs:
      --   {  quot(s(x), s(y)) -> s(quot(minus(x, y), s(y)))
      --    , quot(0(), s(y)) -> 0()
      --    , minus(s(x), s(y)) -> minus(x, y)
      --    , minus(x, 0()) -> x}
      -- StartTerms: basic terms
      -- Strategy: none
      ----------------------------------------------------------------------
      --
      -- After loading is completed, the /current proof state/ is displayed. 
      -- In the example, the proof state consists of the problem loaded from
      -- the file "examples/quot.trs".
      
      -- ** Loading Problems with Respect to a Complexity Category
      -- | For convenience, TcT-i provides the following modifications of 'load', 
      -- matching the categories of the complexity division of 
      -- the internation termination competition 
      -- <http://termination-portal.org/wiki/Complexity>.
    
    , loadRC
      -- | Same as 'load', but overwrites strategy and start-terms 
      -- in order to match a runtime-complexity problem.
    , loadIRC
      -- | Same as 'load', but overwrites strategy and start-terms 
      -- in order to match a innermost runtime-complexity problem.
    , loadDC
      -- | Same as 'load', but overwrites strategy and start-terms 
      -- in order to match a derivational-complexity problem.
    , loadIDC      
      -- | Same as 'load', but overwrites strategy and start-terms 
      -- in order to match a innermost derivational-complexity problem.
      
      -- * The Proof State
      -- | During the interactive session, TcT-i maintains a so called
      -- /proof state/, which is basically a list of /open complexity problems/
      -- together with some information on how this state was obtained. 
      -- In order to prove upper bounds on complexity problem, this 
      -- proof state needs to be reduced to the empty list. 
      -- 
      -- To see the list of open problems, use the action 'state'. 
      -- To obtain a proof, use the action 'proof'. To simplify the state
      -- use the action 'apply' as described below.
      
      -- ** Applying Complexity Techniques
      -- | The proof state is modified by applying instance of processors.
      -- A processor is the TcT representation of a complexity technique. 
      -- Processors are separated for historical reasons into /standard-processors/
      -- and /transformers/. 
      -- 
      -- Processors are usually parameterised by some arguments, for instance the 
      -- dependency pair processor 'Processors.dependencyPairs' accepts a flag 'usetuples'
      -- that defines whether dependency tuples should be employed. 
      -- Processors with instantiated arguments are called /instances of processors/. 
      -- When applying a processor, TcT-i will prompt the user for any necessary arguments
      -- so it can construct the corresponding instance.
      -- 
      -- Predefined processors are available in module "Tct.Processors".      
      -- Instances can be constructed also directly, using the functionality provided in
      -- "Tct.Instances". This module defines also a wealth of combinators and is considered
      -- the preferred way for dealing with processors.
    , apply 
      -- | Type @'apply' m@ for some technique @m@ to simplify the list of selected open problems 
      -- using @m@. 
      -- The proof state is updated by replacing each open problem with the result of applying @m@.
      -- TcT-i displays the proof fragment resulting from applying @m@ to each selected open problem,
      -- and finally redisplays the new proof state.
      -- 
      -- The following example demonstrates the application of dependency pairs.
      -- Note that when a processor from "Tct.Processors" is applied, 
      -- TcT-i might ask for further flags.
      -- 
      -- >>> apply Processor.dependencyPairs
      -- Input arguments for dp
      -- * 'usetuples'
      --   This argument specifies whether dependency tuples instead of pairs
      --   should be used.
      --   Synopsis: On|Off
      --   Use the default value 'Off'? Enter 'yes' or 'no', default is 'yes':
      --   > 
      --   Problem 1:
      --   ----------
      -- 1) Dependency Pairs [OPEN]:
      --   ---------------------------
      -- .  
      --     We consider the following problem:
      --       Strict Trs:
      --         {  quot(s(x), s(y)) -> s(quot(minus(x, y), s(y)))
      --          , quot(0(), s(y)) -> 0()
      --          , minus(s(x), s(y)) -> minus(x, y)
      --          , minus(x, 0()) -> x}
      --       StartTerms: basic terms
      --       Strategy: none
      -- .
      --     We have computed the following dependency pairs
      -- .
      --       Strict DPs:
      --         {  quot^#(s(x), s(y)) -> quot^#(minus(x, y), s(y))
      --          , quot^#(0(), s(y)) -> c_2()
      --          , minus^#(s(x), s(y)) -> minus^#(x, y)
      --          , minus^#(x, 0()) -> x}
      -- .
      --     Generated New Problems:
      --     -----------------------
      -- .
      --       * Problem 1.1)
      --           Strict DPs:
      --             {  quot^#(s(x), s(y)) -> quot^#(minus(x, y), s(y))
      --              , quot^#(0(), s(y)) -> c_2()
      --              , minus^#(s(x), s(y)) -> minus^#(x, y)
      --              , minus^#(x, 0()) -> x}
      --           Strict Trs:
      --             {  quot(s(x), s(y)) -> s(quot(minus(x, y), s(y)))
      --              , quot(0(), s(y)) -> 0()
      --              , minus(s(x), s(y)) -> minus(x, y)
      --              , minus(x, 0()) -> x}
      --           StartTerms: basic terms
      --           Strategy: none
      -- .      
      --       1.1) Open Problem [OPEN]:
      --       -------------------------
      --         We consider the following problem:
      --           Strict DPs:
      --             {  quot^#(s(x), s(y)) -> quot^#(minus(x, y), s(y))
      --              , quot^#(0(), s(y)) -> c_2()
      --              , minus^#(s(x), s(y)) -> minus^#(x, y)
      --              , minus^#(x, 0()) -> x}
      --           Strict Trs:
      --             {  quot(s(x), s(y)) -> s(quot(minus(x, y), s(y)))
      --              , quot(0(), s(y)) -> 0()
      --              , minus(s(x), s(y)) -> minus(x, y)
      --              , minus(x, 0()) -> x}
      --           StartTerms: basic terms
      --           Strategy: none
      -- .
      --   ----------------------------------------------------------------------
      --   Selected Open Problems:
      --   -----------------------
      --     Strict DPs:
      --       {  quot^#(s(x), s(y)) -> quot^#(minus(x, y), s(y))
      --        , quot^#(0(), s(y)) -> c_2()
      --        , minus^#(s(x), s(y)) -> minus^#(x, y)
      --        , minus^#(x, 0()) -> x}
      --     Strict Trs:
      --       {  quot(s(x), s(y)) -> s(quot(minus(x, y), s(y)))
      --        , quot(0(), s(y)) -> 0()
      --        , minus(s(x), s(y)) -> minus(x, y)
      --        , minus(x, 0()) -> x}
      --     StartTerms: basic terms
      --     Strategy: none
      --   ----------------------------------------------------------------------
      -- 
      -- The next example shows the application of instances, in 
      -- combination with the combinators from "Tct.Instances".
      -- 
      -- >>> :module +Tct.Instances
      -- >>> apply $ try removeTails >>> try usableRules 
      -- ...
      -- ----------------------------------------------------------------------
      -- Selected Open Problems:
      -- -----------------------
      --   Strict DPs:
      --     {  quot^#(s(x), s(y)) -> quot^#(minus(x, y), s(y))
      --      , quot^#(0(), s(y)) -> c_2()
      --      , minus^#(s(x), s(y)) -> minus^#(x, y)
      --      , minus^#(x, 0()) -> x}
      --   Strict Trs:
      --     {  minus(s(x), s(y)) -> minus(x, y)
      --      , minus(x, 0()) -> x}
      --   StartTerms: basic terms
      --   Strategy: none
      -- ----------------------------------------------------------------------
      --
    , Apply
      -- | Instance of the class apply can be used to modify 
      -- the list of (selected) open problems using the action 'apply'.
      -- 
      -- Values of type @'StdProcessor' p@ and @'Transformation' t sub@
      -- can be found in module "Tct.Processors".
      -- Values of type @'P.InstanceOf' p@ and @'TheTransformer' t@ for 
      -- (standard) processors @p@ and transformations @t@, i.e., 
      -- instances of processors, are collected in "Tct.Instances".
      
      
      -- ** Inspecting the State
      -- | As explained above, TcT-i retains a list of open problems 
      -- and proof information. These are accessible anytime using the 
      -- actions 'state' and 'proof'. 
    , state
      -- | This action prints the current proof state.
      --
      -- >>> state
      -- ----------------------------------------------------------------------
      -- Selected Open Problems:
      -- -----------------------
      --   Strict DPs:
      --     {  quot^#(s(x), s(y)) -> quot^#(minus(x, y), s(y))
      --      , quot^#(0(), s(y)) -> c_2()
      --      , minus^#(s(x), s(y)) -> minus^#(x, y)
      --      , minus^#(x, 0()) -> x}
      --   Strict Trs:
      --     {  minus(s(x), s(y)) -> minus(x, y)
      --      , minus(x, 0()) -> x}
      --   StartTerms: basic terms
      --   Strategy: none
      -- ----------------------------------------------------------------------
      --
      -- The output shows the example from 'load', already simplified using weak dependency pairs, 
      -- and further processed by @'T.try' 'Instances.removeTails' 'Instances.>>>' 'Instances.try' 'Instances.usableRules'@

    , proof
      -- | This action prints the current proof tree.
      --
      -- >>> proof
      -- 1) Dependency Pairs [OPEN]:
      --   ---------------------------
      -- .  
      --     We consider the following problem:
      --       Strict Trs:
      --         {  quot(s(x), s(y)) -> s(quot(minus(x, y), s(y)))
      --          , quot(0(), s(y)) -> 0()
      --          , minus(s(x), s(y)) -> minus(x, y)
      --          , minus(x, 0()) -> x}
      --       StartTerms: basic terms
      --       Strategy: none
      -- .
      --     We have computed the following dependency pairs
      -- .
      --       Strict DPs:
      --         {  quot^#(s(x), s(y)) -> quot^#(minus(x, y), s(y))
      --          , quot^#(0(), s(y)) -> c_2()
      --          , minus^#(s(x), s(y)) -> minus^#(x, y)
      --          , minus^#(x, 0()) -> x}
      -- .
      --     Generated New Problems:
      --     -----------------------
      -- .
      --       * Problem 1.1)
      --           Strict DPs:
      --             {  quot^#(s(x), s(y)) -> quot^#(minus(x, y), s(y))
      --              , quot^#(0(), s(y)) -> c_2()
      --              , minus^#(s(x), s(y)) -> minus^#(x, y)
      --              , minus^#(x, 0()) -> x}
      --           Strict Trs:
      --             {  quot(s(x), s(y)) -> s(quot(minus(x, y), s(y)))
      --              , quot(0(), s(y)) -> 0()
      --              , minus(s(x), s(y)) -> minus(x, y)
      --              , minus(x, 0()) -> x}
      --           StartTerms: basic terms
      --           Strategy: none
      -- .
      --     1.1) removetails >>> ... [OPEN]:
      --     --------------------------------
      -- .
      --       We consider the following problem:
      --         Strict DPs:
      --           {  quot^#(s(x), s(y)) -> quot^#(minus(x, y), s(y))
      --            , quot^#(0(), s(y)) -> c_2()
      --            , minus^#(s(x), s(y)) -> minus^#(x, y)
      --            , minus^#(x, 0()) -> x}
      --         Strict Trs:
      --           {  quot(s(x), s(y)) -> s(quot(minus(x, y), s(y)))
      --            , quot(0(), s(y)) -> 0()
      --            , minus(s(x), s(y)) -> minus(x, y)
      --            , minus(x, 0()) -> x}
      --         StartTerms: basic terms
      --         Strategy: none
      -- .
      --       The processor is inapplicable since the strict component of the
      --       input problem is not empty
      -- .
      --       We apply the transformation 'usablerules' on the resulting sub-problem(s):
      -- .
      --         We consider the problem
      -- .
      --         Strict DPs:
      --           {  quot^#(s(x), s(y)) -> quot^#(minus(x, y), s(y))
      --            , quot^#(0(), s(y)) -> c_2()
      --            , minus^#(s(x), s(y)) -> minus^#(x, y)
      --            , minus^#(x, 0()) -> x}
      --         Strict Trs:
      --           {  quot(s(x), s(y)) -> s(quot(minus(x, y), s(y)))
      --            , quot(0(), s(y)) -> 0()
      --            , minus(s(x), s(y)) -> minus(x, y)
      --            , minus(x, 0()) -> x}
      --         StartTerms: basic terms
      --         Strategy: none
      -- .
      --         We replace strict/weak-rules by the corresponding usable rules:
      -- .
      --           Strict Usable Rules:
      --             {  minus(s(x), s(y)) -> minus(x, y)
      --              , minus(x, 0()) -> x}
      -- .
      --         The consider problem is replaced by
      -- .
      --         1) Strict DPs:
      --              {  quot^#(s(x), s(y)) -> quot^#(minus(x, y), s(y))
      --               , quot^#(0(), s(y)) -> c_2()
      --               , minus^#(s(x), s(y)) -> minus^#(x, y)
      --               , minus^#(x, 0()) -> x}
      --            Strict Trs:
      --              {  minus(s(x), s(y)) -> minus(x, y)
      --               , minus(x, 0()) -> x}
      --            StartTerms: basic terms
      --            Strategy: none
      -- . 
      --       Generated New Problems:
      --       -----------------------
      -- .
      --         * Problem 1.1.1)
      --             Strict DPs:
      --               {  quot^#(s(x), s(y)) -> quot^#(minus(x, y), s(y))
      --                , quot^#(0(), s(y)) -> c_2()
      --                , minus^#(s(x), s(y)) -> minus^#(x, y)
      --                , minus^#(x, 0()) -> x}
      --             Strict Trs:
      --               {  minus(s(x), s(y)) -> minus(x, y)
      --                , minus(x, 0()) -> x}
      --             StartTerms: basic terms
      --             Strategy: none
      -- .
      --       1.1.1) Open Problem [OPEN]:
      --       ---------------------------
      -- .
      --         We consider the following problem:
      --           Strict DPs:
      --             {  quot^#(s(x), s(y)) -> quot^#(minus(x, y), s(y))
      --              , quot^#(0(), s(y)) -> c_2()
      --              , minus^#(s(x), s(y)) -> minus^#(x, y)
      --              , minus^#(x, 0()) -> x}
      --           Strict Trs:
      --             {  minus(s(x), s(y)) -> minus(x, y)
      --              , minus(x, 0()) -> x}
      --           StartTerms: basic terms
      --           Strategy: none
      --
      -- The output precisely reflects how the current proof state was 
      -- obtained from the initial state. Since 'state' contains still open problems, 
      -- the proof also open subproblems, in this case 
      -- subproblem 1.1.1).
      -- From the output we can also see that 'Instances.removeTails' is inapplicable. 
      -- The reason is that 'Instances.removeTails' is unsound if the strict trs
      -- from the problem is not empty. TcT will never apply processors in an unsound
      -- setting!

      -- ** Extracting the State
      -- | Beside showing the current state and the proof constructed so far, 
      -- TcT-i also defines actions for extractions.
    , problems
      -- | Displays and returns the list of selected open problems.
      -- 
      -- >>> problems
      -- Problem 1:
      -- . 
      --   Strict DPs:
      --   {  quot^#(s(x), s(y)) -> quot^#(minus(x, y), s(y))
      --   , quot^#(0(), s(y)) -> c_2()
      --   , minus^#(s(x), s(y)) -> minus^#(x, y)
      --    , minus^#(x, 0()) -> x}
      -- Strict Trs:
      --   {  minus(s(x), s(y)) -> minus(x, y)
      --    , minus(x, 0()) -> x}
      -- StartTerms: basic terms
      -- Strategy: none
      -- .
      -- [Problem { startTerms = ...
      --          , strategy   = ...
      --          , variables  = ...
      --          , signature  = ...
      --          , strictDPs  = Trs {rules = ...} 
      --          , strictTrs  = Trs {rules = ...} 
      --          , weakDPs    = Trs {rules = ...} 
      --          , weakTrs    = Trs {rules = ...}}
      -- ]
      -- 
      -- Problems are defined in the accompanying /term rewriting library/
      -- (cf. <http://cl-informatik.uibk.ac.at/software/tct/projects/termlib/>).
      -- The module 'Termlib.Repl', collecting most of the functionality of  
      -- the term rewriting library, is imported qualified as module 'TR'. Cf.
      -- <http://cl-informatik.uibk.ac.at/software/tct/projects/termlib/docs/Termlib-Repl.html>
      -- for documentation of the module 'Termlib.Repl'.
    , wdgs
      -- | This action displays the weak dependency graphs of all selected
      -- problems. If 'dot' from the GraphViz project (c.f. <http://www.graphviz.org/>) 
      -- is installed, then a SVG-picture is rendered in 'dg.svg' of
      -- the current working directory.
    , cwdgs
      -- | This action displays the weak congruence dependency graphs of all 
      -- selected problems. To produce an SVG-picture, use the procedure
      -- 'wdgs' that draws weak dependency graphs, but also shows
      -- congruence classes.
    , uargs      
      -- | This action displays the argument positions of the selected problems.

      
      -- ** Selecting and Unselecting Problems #Select#      
      -- | Sometimes it is convenient to consider a sublist of the list
      -- of open Problems. To restrict the list of problems considered
      -- by 'apply', use the procedures 'select' and 'unselect', 
      -- in combination with a 'Selector'. 
    , Selector 
      -- | Instances of this class can be used in combination with 
      -- select. Note that Selector @['Int']@  selects according to the 
      -- problem number as recorded in the state (c.f. procedure 'state').
    , select
      -- | Select problems from the proof state according to the given 'Selector'.
      -- 
      -- Consider the following state that is obtained from the running example, 
      -- after applying 'Instances.pathAnalysis'.
      --
      -- >>> state
      -- --------------------------------------------------------------------
      -- Selected Open Problems:
      -- -----------------------
      --   1) Strict DPs: {minus^#(s(x), s(y)) -> minus^#(x, y)}
      --      Strict Trs:
      --        {  minus(s(x), s(y)) -> minus(x, y)
      --         , minus(x, 0()) -> x}
      --      StartTerms: basic terms
      --      Strategy: none
      -- .
      --   2) Strict DPs: {minus^#(x, 0()) -> x}
      --      Strict Trs:
      --        {  minus(s(x), s(y)) -> minus(x, y)
      --         , minus(x, 0()) -> x}
      --      Weak DPs: {minus^#(s(x), s(y)) -> minus^#(x, y)}
      --      StartTerms: basic terms
      --      Strategy: none
      -- .
      --   3) Strict DPs: {quot^#(s(x), s(y)) -> quot^#(minus(x, y), s(y))}
      --      Strict Trs:
      --        {  minus(s(x), s(y)) -> minus(x, y)
      --         , minus(x, 0()) -> x}
      --      StartTerms: basic terms
      --      Strategy: none
      -- .
      --   4) Strict DPs: {quot^#(0(), s(y)) -> c_2()}
      --      Strict Trs:
      --        {  minus(s(x), s(y)) -> minus(x, y)
      --         , minus(x, 0()) -> x}
      --      Weak DPs: {quot^#(s(x), s(y)) -> quot^#(minus(x, y), s(y))}
      --      StartTerms: basic terms
      --      Strategy: none
      -- .
      -- >>> select [1,3]
      -- --------------------------------------------------------------------
      -- Unselected Open Problems:
      -- -------------------------
      --   2) Strict DPs: {minus^#(x, 0()) -> x}
      --      Strict Trs:
      --        {  minus(s(x), s(y)) -> minus(x, y)
      --         , minus(x, 0()) -> x}
      --      Weak DPs: {minus^#(s(x), s(y)) -> minus^#(x, y)}
      --      StartTerms: basic terms
      --      Strategy: none
      -- .
      --   4) Strict DPs: {quot^#(0(), s(y)) -> c_2()}
      --      Strict Trs:
      --        {  minus(s(x), s(y)) -> minus(x, y)
      --         , minus(x, 0()) -> x}
      --      Weak DPs: {quot^#(s(x), s(y)) -> quot^#(minus(x, y), s(y))}
      --      StartTerms: basic terms
      --      Strategy: none
      -- .
      -- Selected Open Problems:
      -- -----------------------
      --   1) Strict DPs: {minus^#(s(x), s(y)) -> minus^#(x, y)}
      --      Strict Trs:
      --        {  minus(s(x), s(y)) -> minus(x, y)
      --         , minus(x, 0()) -> x}
      --      StartTerms: basic terms
      --      Strategy: none
      -- .
      --   3) Strict DPs: {quot^#(s(x), s(y)) -> quot^#(minus(x, y), s(y))}
      --      Strict Trs:
      --        {  minus(s(x), s(y)) -> minus(x, y)
      --         , minus(x, 0()) -> x}
      --      StartTerms: basic terms
      --      Strategy: none
      -- 
      --
    , unselect
      -- | Inverse of 'select'. The example of 'select' can also be obtained by typing
      --
      -- >>> unselect [2,4]
      -- 
    , SelectAll
      -- | Special selector to select all open problems.
    , SelectInv
      -- | Special selector to inverse a selection.
      
      -- ** Changing the Initial Problem
      -- | The following procedures change the initial problem. 
      -- Note that in order to guarantee soundness, any progress
      -- will undone. However the procedure 'undo' allows to revert 
      -- a change to the initial problem.
    , setRC
      -- | This action overwrites strategy and start-terms 
      -- in order to match a runtime-complexity problem.
    , setIRC
      -- | This action overwrites strategy and start-terms 
      -- in order to match a innermost runtime-complexity problem.
    , setDC
      -- | This action overwrites strategy and start-terms 
      -- in order to match a derivational-complexity problem.
    , setIDC      
      -- | This action overwrites strategy and start-terms 
      -- in order to match a innermost derivational-complexity problem.
      
    , addRuleFromString
      -- | This action adds the given rule to the input problem. 
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
      -- | This action deletes the given rule from the input problem. See 'addRuleFromString'
      -- for grammar.
      
    , modifyInitialWith      
      -- | This action modifies the initial problem according to given function.
      
      -- * History Functionality
      -- | TcT provides basic history functionality, in order to undo previous actions. 
      -- This functionality covers all actions that modify the state.
      
    , reset
      -- | This action resets the proof state to the initially loaded system.
    , undo
      -- | Undos the last modification of the proof state
      
      -- * Help and Documentation
    , help
      -- | Displays a help message.
    , welcome
      -- | Displays a help message.
    , describe
      -- | Prints a description of the given technique. In particular, 
      -- 'describe' accepts processors as defined in 'Tct.Processors'.
      -- 
      -- >>>describe Processor.lmpo
      -- .
      -- Processor "lmpo":
      -- -----------------
      --   This processor implements orientation of the input problem using
      --   'light multiset path orders',
      --   a technique applicable for innermost runtime-complexity analysis.
      --   Light multiset path orders are a miniaturisation of 'multiset path
      --   orders', restricted so that compatibility assesses polytime computability 
      --   of the functions defined.
      --   Further, it induces exponentially bounded innermost runtime-complexity.
      -- .   
      --   Usage:
      --    lmpo [:ps [On|Off]] [:wsc [On|Off]]
      -- .      
      --   Arguments:
      --    ps:
      --              If enabled then the scheme of parameter substitution is admitted,
      --              cf. http://cl-informatik.uibk.ac.at/~zini/publications/WST09.pdf
      --              how this is done for polynomial path orders.
      --              The default is set to 'On'.
      -- . 
      --    wsc:
      --              If enabled then composition is restricted to weak safe composition.
      -- .
      -- For documentation concerning creation of instances, consult:
      --   http://cl-informatik.uibk.ac.at/software/tct/projects/tct/docs/Tct-Instances.html#v:lmpo
      -- 
    , Describe 
      -- | Instances of this class can be handled by the action 'describe'.
      
      -- * Miscellaneous Utilities
    , pprint
      -- | pretty-print objects.
    , termFromString
      -- | Parses a term from a string, with respect
      -- to the signature and variables from the given problem.
      -- See 'addRuleFromString' for grammar.      
    , ruleFromString
      -- | Parses a rule from a string, with respect
      -- to the signature and variables from the given problem.
      -- See 'addRuleFromString' for grammar.            
      
      -- * Accessing to the Configuration
      -- | The TcT configuration file, usually residing in @${HOME}\/.tct\/tct.hs@ contains
      -- a definition @config :: 'Config'@. 
      -- In particular, TcT-i employs the field @processors@ when it requires the list
      -- of available processors, for instance when parsing arguments.
      -- The configuration is accessible throught the following actions.
      -- Note that the configuration can be modified while running TcT-i.
    , getConfig
      -- | Returns the current configuration.      
    , setConfig
      -- | Set the configuration.      
    , modifyConfig
      -- | Modify the configuration according to the given function.      
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

import Tct (Config, defaultConfig)
import qualified Tct as Tct
import qualified Tct.Processors as Processors ()
import qualified Tct.Instances as Instances ()
import Tct.Utils.PPrint
import Tct.Utils.Enum
import Tct.Main.Version (version)
import qualified Tct.Processor as P
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances ()
import qualified Tct.Processor.Standard as S
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
               | Transformed Bool Problem (T.TheTransformer T.SomeTransformation) (T.ProofOf T.SomeTransformation) (Enumeration ProofTree)
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
        proc = tinst T.>>| seqProc                                         
        tproof = 
          T.Proof { T.transformationResult = 
                       case progressed of 
                         True  -> T.Progress tres $ mapEnum P.inputProblem subproofs
                         False -> T.NoProgress tres
                  , T.inputProblem        = prob
                  , T.appliedTransformer  = tinst
                  , T.appliedSubprocessor = T.mkSubsumed seqProc
                  , T.subProofs           = toSeqProof `mapEnum` subproofs }
        

problemFromTree :: ProofTree -> Problem 
problemFromTree = P.inputProblem . proofFromTree

--------------------------------------------------------------------------------
--- State

data ST = ST { unselected :: ![SomeNumbering]
             , proofTree  :: Maybe ProofTree}
         

data STATE = STATE ST [ST] 

curState :: STATE -> ST
curState (STATE st _) = st
                                 
configRef :: IORef Config
configRef = unsafePerformIO $ newIORef defaultConfig
{-# NOINLINE configRef #-}

setConfig :: Config -> IO ()
setConfig = writeIORef configRef

getConfig :: IO Config
getConfig = readIORef configRef

configDirectory :: IO FilePath
configDirectory = 
  do cfg <- getConfig
     efp <- Tct.runErroneous $ Tct.configDir cfg
     return $ case efp of 
       Left _ -> "~/.tct/"
       Right fp -> fp
     
modifyConfig :: (Config -> Config) -> IO ()
modifyConfig f = do c <- getConfig
                    setConfig $ f c
                    
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

instance (Integral n) => Selector [n] where  
  selct ep is = [j | (j,_) <- ep, j `elem` [fromInteger $ toInteger i | i <- is]]

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
select sel = unselect $ SelectInv sel


--------------------------------------------------------------------------------
--- Actions 

                        
class Apply p where
  apply' :: p -> Enumeration Problem -> IO (SomeNumbering -> Problem -> Maybe ProofTree)
  
apply :: Apply p => p -> IO ()
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
    do mrs <- runTct $ evalEnum False [ (i, T.sanitiseResult `liftM` T.transform tinst prob) | (i, prob) <- selected ]
       case mrs of 
         Nothing -> 
           error "error when transforming some problem"
         Just rs -> 
           return $ \ (SN sn) prob -> mkNode prob `fmap` (find sn rs)
          where mkNode prob res = Transformed progressed prob tinst tproof subTrees
                  where progressed = T.isProgressResult res
                        tproof = T.proofFromResult res
                        subTrees | progressed = Open `mapEnum` T.subProblemsFromResult res
                                 | otherwise  = enumeration' [Open prob] 
      where tinst = T.someTransformation t         
                                      
instance P.Processor p => Apply (P.InstanceOf p) where
  apply' p selected =   
    do mrs <- runTct $ evalEnum False [ (i, P.solve pinst prob) | (i, prob) <- selected ]
       case mrs of 
         Nothing -> error "error when solving some problem"
         Just rs -> return $ \ (SN sn) prob -> mkNode prob `fmap` (find sn rs)
      where mkNode prob res | P.succeeded res = Closed prob pinst res
                            | otherwise       = Open prob
            pinst = P.someInstance p
                
--------------------------------------------------------------------------------
--- Description            
            
class Describe p where
  describe :: p -> IO ()
  
instance (S.Processor p, A.ParsableArguments (S.ArgumentsOf p)) => Describe (S.StdProcessor p) where
  describe p = 
    do mlnk <- haddockInstances (P.name p) 
              `Ex.catch` (\ (_ :: Ex.SomeException) -> return Nothing)
       pprint (P.someProcessor p)
       pprint $ maybe empty showLnk mlnk
    where showLnk lnk = text "For documentation concerning creation of instances, consult:"
                        $+$ indent (text lnk)
                        
instance (T.Transformer t, A.ParsableArguments (T.ArgumentsOf t)) => Describe (T.Transformation t P.AnyProcessor) where            
  describe = describe . S.StdProcessor

instance (T.Transformer t) => Show (T.Transformation t sub) where
  show (T.Transformation t) = "<transformation " ++ T.name t ++ ">"

instance (S.Processor p) => Show (S.StdProcessor p) where
  show (S.StdProcessor p) = "<processor " ++ S.name p ++ ">"

allProcessors :: IO (P.AnyProcessor)
allProcessors = Tct.processors `liftM` getConfig
                   
transformation :: (T.Transformer t, A.ParsableArguments (T.ArgumentsOf t)) => t -> IO (T.TheTransformer t)
transformation trans = 
  do procs <- allProcessors
     putStrLn $ "Input arguments for " ++ T.name trans
     mkInst `liftM` A.parseInteractive (T.arguments trans) procs
  where mkInst args = (T.Transformation trans) `T.withArgs` args

processor :: (A.ParsableArguments (S.ArgumentsOf p), S.Processor p) => p -> IO (P.InstanceOf (S.StdProcessor p))
processor proc = 
    do procs <- allProcessors
       putStrLn $ "Input arguments for " ++ S.name proc
       mkInst `liftM` A.parseInteractive (S.arguments proc) procs
  where mkInst args = (S.StdProcessor proc) `S.withArgs` args
          
-- instance Apply P.SomeProcessor where
--   apply' (P.SomeProcessor p) = 
--     case cast p of 
--       Just (S.StdProcessor (T.Transformation t)) -> undefined
    
instance (A.ParsableArguments (S.ArgumentsOf p), S.Processor p) => Apply (S.StdProcessor p) where
  apply' (S.StdProcessor proc) selected = 
    do inst <- processor proc
       apply' inst selected
    
instance (A.ParsableArguments (T.ArgumentsOf t), T.Transformer t) => Apply (T.Transformation t sub) where
  apply' (T.Transformation t) selected = 
    do inst <- transformation t
       apply' inst selected



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

haddockInstances :: String -> IO (Maybe String)
haddockInstances name = 
  do mpt <- haddockPath ("tct-" ++ version) 
     case mpt of 
       Nothing -> 
         do pprint (text "Could not find documentation installed on your system."
                    $+$ text ""
                    $+$ nb "Use 'cabal haddock && cabal install' in the source-director of tct to install documentation.")
            return Nothing
       Just pt -> 
         return $ Just $ "file://" ++ pt ++ "/Tct-Instances.html#v:" ++ name


welcome :: IO ()
welcome = pprint $ 
  U.underline (text ("Welcome to the TcT"))
  $+$ text ""
  $+$ U.paragraph ("This is version " 
                   ++ version 
                   ++ " of the Tyrolean Complexity Tool.")
  $+$ text ""                    
  $+$ text "(c)" <+> ( text "Martin Avanzini <martin.avanzini@uibk.ac.at>,"
                       $+$ text "Georg Moser <georg.moser@uibk.ac.at>, and"
                       $+$ text "Andreas Schnabl <andreas.schnabl@uibk.ac.at>.")
  $+$ text ""
  $+$ U.paragraph ("This software is licensed under the GNU Lesser "
                   ++ "General Public License, see <http://www.gnu.org/licenses/>.")
  $+$ text ""
  $+$ text "Don't know how to start? Type 'help'."

help :: IO ()
help = do cfgdir <- configDirectory
          localdoc <- haddockPath ("tct-" ++ version) 
          tllocaldoc <- haddockPath ("termlib")
          let remoteurl = "http://cl-informatik.uibk.ac.at/software/tct/projects/tct/docs"
              tlremoteurl = "http://cl-informatik.uibk.ac.at/software/tct/projects/termlib/docs"
              docurl = fromMaybe remoteurl localdoc
              tldocurl = fromMaybe tlremoteurl tllocaldoc              
              lst s ls = vcat [text s <+> l | l <- ls]
              msg = U.paragraph ("This is version " 
                                 ++ version 
                                 ++ " of the Tyrolean Complexity Tool.")
                    $+$ text ""
                    $+$ U.underline (text "Getting Started:")
                    $+$ text ""
                    $+$ indent (lst "*" 
                                [ text "Use 'load \"<filename>\" to load a problem."
                                , U.paragraph ("Use 'apply <technique>' to simplify the loaded problem. "
                                               ++ "Here <technique> can be one of the following")
                                  $+$ indent (lst "-"
                                              [ U.paragraph ("A processor as collected in module 'Processor'. In this case, "
                                                             ++ "TcT will prompt for any needed arguments.")
                                              , U.paragraph ("An instance of a processor obtained by one of "
                                                             ++ "the constructors from module 'Instance'.")
                                              ])
                                , U.paragraph ( "Use 'describe <processor>' to obtain documentation for "
                                                ++ "the processor <processor>, c.f. module 'Processor' for a list "
                                                ++ "of available processors.")
                                , U.paragraph ( "Type 'state' to output the current proof state.")
                                , U.paragraph ( "Type 'proof' to output the proof constructed so far.")                                  
                                , U.paragraph ( "Modify the configuration file '" ++ cfgdir ++ "/tct.hs' "
                                                ++ " which is automatically loaded on startup.")
                                , U.paragraph ( "Type ':quit' to exit Tct. ")
                                ])
                    $+$ text ""
                    $+$ text "This message is available by typing 'help'."
                    $+$ text ""
                    $+$ U.underline (text "Further Help:")
                    $+$ text ""
                    $+$ indent (text "Consult the following pages concering"
                                $+$ indent (lst "*"
                                            [ text "interactive interface:"
                                              $+$ indent (text (docurl ++ "/Tct-Interactive.html"))
                                            , text "general help on TcT:"
                                              $+$ indent (text (docurl ++ "/index.html"))
                                            , text "the rewriting library:"
                                              $+$ indent (text (tldocurl ++ "/index.html")) ]))
          pprint msg
          
              
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

pprintIth :: U.PrettyPrintable p => String -> (Int,p) -> IO ()
pprintIth nm (i,p) = pprint (text nm <+> text (show i) <> text ":"
                             $+$ indent (U.pprint p))

problems :: IO [Problem]
problems = 
  do ps <- problems'
     mapM_ (pprintIth "Problem")  $zip [1..] ps
     return ps
     

wdgs :: IO [DG.DG]   
wdgs = do probs <- problems'
          let dgs = [ (DG.estimatedDependencyGraph DG.Edg prob
                       , Prob.signature prob 
                       , Prob.variables prob) 
                    | prob <- probs ]
          fn <- getCurrentDirectory          
          _ <- forkIO (DG.saveGraphViz dgs "dg.svg" >> return ())
          mapM_ (pprintIth "Weak Dependency Graph of Problem") $ zip [1..] dgs
          putStrLn $ "\nsee also '" ++ fn ++ "/dg.svg'.\n"
          return [dg | (dg,_,_) <- dgs]

cwdgs :: IO [DG.CDG]
cwdgs = (zip [1..] `liftM` problems') >>= mapM f                            
  where f (i,prob) = 
          do let dg = DG.toCongruenceGraph $ DG.estimatedDependencyGraph DG.Edg prob
             pprintIth "Congruence Graph of Problem" (i,(dg,Prob.signature prob,Prob.variables prob))
             return dg

uargs :: IO [UA.UsablePositions]
uargs = (zip [1..] `liftM` problems') >>= mapM f
    where f (i,prob) = pprintIth "Usable Arguments with Repect to Problem" (i, (ua, sig)) >> return ua
            where ua = UA.usableArgs (Prob.strategy prob) (Prob.allComponents prob)
                  sig = Prob.signature prob

termFromString :: String -> Problem -> IO (Term, Problem)
termFromString str prob = do pprint term
                             return r
  where r@(term,_) = TRepl.parseFromString TParser.term str prob

ruleFromString :: String -> Problem -> IO (Rule, Problem)
ruleFromString str prob = do pprint rl
                             return (rl,prob')
  where ((_,rl),prob') = TRepl.parseFromString TParser.rule str prob
        

