#!/usr/bin/python3

import subprocess
import os
import shutil
import sys
from mako.template import Template

MIN_K           = 1
MAX_K           = 25
MAX_TIME        = 1 * 60 * 60 # 1 Hours
TERMITE_SAT     = ".cabal-sandbox/bin/TermiteSAT"

TSL_DIR         = "specs/tsl-files"
M4_DIR          = "specs/"
LOGFN           = "benchmarks.log"
FAMILIES        = [
      "queue"
    , "queue_fails"
    , "spi"
    , "uart"
    , "ide"
    ]

M4FILE          = {
                  "spi" : "spi.m4"
                , "queue" : "queue.m4"
                , "queue_fails" : "queue_fails.mako"
                , "ide"  : "ide.m4"
                , "uart"  : "uart.m4"
                }

M4PARAM         = {
                  "spi" : "QSIZE"
                , "queue" : "qlen"
                , "queue_fails" : "qlenf"
                , "ide"  : "NFRAGS"
                , "uart"  : "FIFOLEN"
                }

MAX_K_F = {
           "spi"            : 4
         , "queue"          : 4
         , "queue_fails"    : 10
         , "ide"            : 4
         , "uart"           : 4
         }

#Clear logfile
f = open(LOGFN, 'w')
f.close()

LOGFILE = open(LOGFN, 'a')

def call_termite_sat(family, scale, args=None):
    dn = open(os.devnull, 'w')
    timedout = False
    ret = 1

    fullargs = []
    if not (args == None):
        fullargs = list(args)
    fullargs.insert(0, TERMITE_SAT)
    fullargs = fullargs + ["-d0"]
    tslfn = TSL_DIR + "/" + family + str(scale) + ".tsl"
    fullargs = fullargs + [tslfn]

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

    templatefile = M4_DIR + M4FILE[family]

    if M4FILE[family].endswith("mako"):
        t = Template(filename=templatefile)
        tslfile.write(t.render(param=scale))
    else:
        subprocess.call(["m4", "-D", M4PARAM[family]+"="+str(scale), templatefile], stdout=tslfile)

    tslfile.close()

families = FAMILIES
if sys.argv[-1] in FAMILIES:
    families = [sys.argv[-1]]

for f in families:
    for k in range(MIN_K, MAX_K_F[f]+1):
        timeout = False
        description = f + " " + str(k)
        print(description)
        LOGFILE.write("*****\n")
        LOGFILE.write("DESC " + description + "\n")
        LOGFILE.flush()
        make_tsl(f, k)
        if not '-b' in sys.argv:
            (timeout, error) = call_termite_sat(f, k)
            LOGFILE.write("*****\n")
            LOGFILE.flush()
            if timeout:
                print("Timed out")
                break
            elif error:
                print("Error!!!")
                break

LOGFILE.close()
