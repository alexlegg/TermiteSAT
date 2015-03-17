TermiteSAT
==========

Termite driver synthesis tool using SAT

Build cudd
    $ cd $PATH-TO-TERMITESAT%/cudd
    $ mv Makefile.64bit Makefile
    $ make libso
    $ sudo vim /etc/ld.so.conf.d/cuddLibs.conf
    %PATH-TO-TERMITESAT%/cudd/libso
    $ sudo ldconfig

Add dependencies to TermiteSAT
    $ cd %PATH-TO-TERMITESAT%
    $ cabal sandbox add-source haskell\_cudd

Add to cabal.config:
extra-include-dirs: %PATH-TO-TERMITESAT%/cudd/include
extra-lib-dirs: %PATH-TO-TERMITESAT%/cudd/libso
