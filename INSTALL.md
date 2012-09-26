This documents describes the procedure for building TCT from source.


Prerequirements
===============
TcT can currently only be installed under GNU/Linux.

Installation
------------
- The [Glasgow Haskell Compiler, version 7.4](http://www.haskell.org/ghc/) or above
- [Cabal Install, version 0.14.0](http://hackage.haskell.org/package/cabal-install) 
  or above for installation using cabal
- The latest versions of packages 'parfold', 'qlogic' and 'termlib', available from 
  the [TcT subproject page](http://cl-informatik.uibk.ac.at/software/tct/projects/index.php).
  These packages are provided by the 
  [TcT bundle](http://cl-informatik.uibk.ac.at/software/tct/projects/tct/archive/tct-bundle-current.tar.gz).

Running
-------
To run TcT, [Minisat version 2.2](http://minisat.se/MiniSat.html) is required.


Installation
============
The preferred way to install TcT is using the 
[TcT bundle distribution](http://cl-informatik.uibk.ac.at/software/tct/projects/tct/archive/tct-bundle-current.tar.gz), 
which contains all required packages not available on hackage.
If you downloaded the bundle distribution, installation is as simple as:

    tar xvzf tct-bundle-current.tar.gz
    cd tct-bundle
    ./install.sh

This will install TcT and its libraries under `~/.cabal`, the executable
can be found under `~/.cabal/bin/`.

Alternatively, one can install the packages 'parfold', 'qlogic', 'termlib' and 'tct' 
separately using cabal-install. This is the preferred way if you are not interested
with cabal-install defaults. To install the packages, follow the general 
[cabal install](http://www.haskell.org/haskellwiki/Cabal/How_to_install_a_Cabal_package) procedure.
To install documentation, use the command `cabal haddock` before `cabal install`.


