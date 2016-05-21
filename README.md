TermiteSAT
==========

Realisability solver based on SAT.

### Installation

You can install the dependencies and run the build script:
```
sudo apt-get install zlib1g-dev autoconf libtool g++ bison flex
./build.sh
```

Alternatively, you can install everything individually:

Get all of the code
```
git clone https://github.com/alexlegg/TermiteSAT
cd TermiteSAT
git submodule init
git submodule update
```

Install Stack: http://www.haskellstack.org/

Build Glucose
You may need to install zlib first (zlib1g-dev on Ubuntu)
```
cd glucose/simp
LIB=glucose make libs
cd ../../
```

Build PeRIPLO
Follow these instructions: https://code.google.com/archive/p/periplo/wikis/BuildPeRIPLOFromSources.wiki
Or, in short:
```
cd periplo
sudo apt-get install autoconf libtool g++ bison flex
wget ftp://ftp.gmplib.org/pub/gmp-5.1.1/gmp-5.1.1.tar.bz2
tar jxvf gmp-5.1.1.tar.bz2
cd gmp-5.1.1
./configure --enable-cxx
make
make check
sudo make install
cd ..
libtoolize
autoreconf --install --force
mkdir build
cd build
../configure --enable-library --enable-proof
make
cd ../../
```

Build CUDD
```
cd cudd
./configure --enable-dddmp --enable-shared
make
make check
sudo make install
cd ..
```

Build TermiteSAT
```
stack setup
stack build
stack install
```

### Usage

```
TermiteSAT [-d<n>] [-i<n>] [-k<n>] [-h<n>] [-p] [-y] 
```

`-d<n>` Debugging output level.

0 = None (default)
1 = Output at end
2 = Dump throughout
3 = Dump after each iteration

`-i<n>` The number of algorithm iterations to use initial state generalisation.
(Default is 3)

`-k<n>` Solve bounded reachability only with a particular bound.

`-h<n>` Strategy shortening

0 = No strategy shortening
1 = Shorten Existential player strategies (default)
2 = Shorten Universal player strategies
3 = Shorten both player's strategies

`-p` Portfolio solver. Runs TermiteSAT in parallel with Simple BDD Solver.

`-y` Hybrid portfolio solver. Share must-losing states from TermiteSAT to
Simple BDD Solver.
