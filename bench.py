#!/usr/bin/python3

import subprocess
import os
import shutil
import sys

MIN_K           = 1
MAX_K           = 25
MAX_TIME        = 1 * 60 * 60 # 1 Hours
TERMITE_SAT     = ".cabal-sandbox/bin/TermiteSAT"
TESTS           = [ ("Base", []) ]
TSL_DIR         = "specs/tsl-files"
M4_DIR          = "specs/"
LOGFN           = "benchmarks.log"
FAMILIES        = ["queue", "spi", "uart", "ide"]
###FAMILIES        = ["spi"]
M4FILE          = {
                  "spi" : "spi.m4"
                , "queue" : "queue.m4"
                , "ide"  : "ide.m4"
                , "uart"  : "uart.m4"
                }
M4PARAM         = {
                  "spi" : "QSIZE"
                , "queue" : "qlen"
                , "ide"  : "NFRAGS"
                , "uart"  : "FIFOLEN"
                }

KVAL = {}
for f in FAMILIES:
    KVAL[f] = {}

MAX_K_F = {"spi" : 8,
         "queue" : 13,
         "ide"  : 5,
         "uart"  : 13 }

###MAX_K_F = {"spi" : 9,
###         "queue" : 4,
###         "ide"  : 4,
###         "uart"  : 4 
###         }

for k in range(1, MAX_K+1):
    KVAL["spi"][k] = (k*2) + 4
    KVAL["queue"][k] = (k*3)
    KVAL["ide"][k] = k + 19
    KVAL["uart"][k] = (k*3) + 5

#Clear logfile
f = open(LOGFN, 'w')
f.close()

LOGFILE = open(LOGFN, 'a')

def call_termite_sat(family, scale, args=None):
    dn = open(os.devnull, 'w')
    timedout = False
    ret = 1

    fullargs = list(args)
    fullargs.insert(0, TERMITE_SAT)
    fullargs = fullargs + ["-d0"]
    fullargs = fullargs + ["-k", str(KVAL[family][scale])]
    tslfn = TSL_DIR + "/" + family + str(scale) + ".tsl"
    fullargs = fullargs + [tslfn]
    print(" ".join(fullargs))

    try:
        ret = subprocess.call(fullargs, stdout=LOGFILE, stderr=dn, timeout=MAX_TIME)
    except subprocess.TimeoutExpired:
        LOGFILE.write("Timed out\n")
        timedout = True

    LOGFILE.flush()
    dn.close()
    return (timedout, (ret != 0))

def make_tsl(family, scale):
    if not os.path.exists(TSL_DIR):
        os.makedirs(TSL_DIR)

    tslfn = TSL_DIR + "/" + family + str(scale) + ".tsl"
    tslfile = open(tslfn, 'w')
    subprocess.call(["m4", "-D", M4PARAM[family]+"="+str(scale), M4_DIR + M4FILE[family]], stdout=tslfile)
    tslfile.close()

for (name, test) in TESTS:
    for f in FAMILIES:
        for k in range(MIN_K, MAX_K_F[f]+1):
            timeout = False
            description = name + " : " + f + " " + str(k)
            print(description)
            LOGFILE.write("*****\n")
            LOGFILE.write("DESC " + description + "\n")
            LOGFILE.flush()
            make_tsl(f, k)
            if not '-b' in sys.argv:
                (timeout, error) = call_termite_sat(f, k, args=test)
                LOGFILE.write("*****\n")
                LOGFILE.flush()
                if timeout:
                    print("Timed out")
                    break
                elif error:
                    print("Error!!!")
                    break

LOGFILE.close()
