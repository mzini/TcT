{- |
Module      :  Tct.Main
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
License     :  LGPL (see COPYING)

Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      


This section covers usage information of the /command line interface/
of TcT, for usage information on the /interactive interface/, please 
refer to "Tcti". As explained in "Tct.Configuration", TcT can be easily 
customized.
TcT is invoked from the command line as follows:

>>> tct [<options>]* <filename>

Here '<filename>' specifies a complexity problem either
in the old /termination problem database/ format (cf. <http://www.lri.fr/~marche/tpdb/format.html>)
or in the new xml-based format (cf. <http://dev.aspsimon.org/xtc.xsd>).
Examples are available in the directory 'examples' in the software distribution, 
or the current termination problem database 
(<http://termcomp.uibk.ac.at/status/downloads/tpdb-current-exported.tar.gz>).
Be sure that you have the SAT-Solver 'minisat' (cf. <http://minisat.se/>)
installed on your system.

If invoked as above, TcT will apply the /default processor/ on the 
input problem. 
A processor is the TcT terminology of an object that guides the proof 
search. 
The option '-s \"\<processor\>\"' allows the specification of the 
particular processor employed by TcT. The syntax of processors 
follows a simple LISP-like language, where a processor is invoked
as 

>>> (name [:opt v]* [pos]*)

Here 'name' refers to the processor name, ':opt v' 
sets the /optional argument/ 'opt' to 'v', and 'pos'
are zero or more positional arguments. 
In addition, outermost paranthesis can be dropped.
See module "Tct.Processors"
for further documentation on processors, and a complete list
of available processors.
The following lines properly construct processors

>>> popstar
>>> popstar :ps On
>>> matrix :dim 1
>>> fastest (popstar :ps On) (matrix :dim 1)
>>> uncurry (fastest (popstar :ps On) (matrix :dim 1))


In addition, TcT supports the following command line options

[--timeout \<num>]
Maximum running time in seconds.

[-t \<num>]
Same as '-timeout'.

[--verbosity \< answer | proof | strategy | a | p | s >]
Verbosity of proof mode.
answer: print only answer from proof
proof: print the full proof
strategy: print the full proof, enriched with strategy information
a: like answer
p: like proof
s: like strategy

[-v \< answer | proof | strategy | a | p | s >]
Same as '-verbosity'.

[--answer \< dc | rc | irc | idc | dc! | rc! | irc! | idc! >]
Overwrite problem specification. Can be one of the following:
dc: derivational complexity
idc: innermost derivational complexity
rc: runtime complexity
irc: innermost runtime complexity
Add '!' at the end to throw an error if problem specification and
given option conflict.

[-a \< dc | rc | irc | idc | dc! | rc! | irc! | idc! >]
Same as '-answer'.

[--minisat \<file>]
Specify the path to the minisat SAT-solver executable.

[-m \<file>]
Same as '-minisat'.

[--processor \<string>]
Specifies the strategy. For a list of strategies see '-l'.

[-s \<string>]
Same as '-processor'.

[--processorfile \<file>]
Like '-s', but reads the strategy from the given file.

[-S \<file>]
Same as '-processorfile'.

[--list \<string>]
Prints a full list of processors.

[-l \<string>]
Same as '-list'.

[--logfile \<file>]
Enable logging. Logging output is sent to specified file.

[-g \<file>]
Same as '-logfile'.

[--help ]
Displays this help message.

[-h ]
Same as '-help'.

[--version ]
Displays the version number.

[-z ]
Same as '-version'.

[--norecompile ]
No recompilation of the binaries.

[-r ]
Same as '-norecompile'.

[--interactive ]
Start TcT in interactive mode.

[-i ]
Same as '-interactive'.

-}


module Tct.Main (
  main
  ) where

import Tct

-- | This is the main function of the executable 'tct'
main :: IO ()
main = tct defaultConfig


