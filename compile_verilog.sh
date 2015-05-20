#!/bin/bash

vl2mv $1

NAME=${1%.*}

~/src/demiurge-1.1.0/tool/build/src/3rd_party/abc/abc/abc -c "read_blif_mv ${NAME}.mv; strash; refactor; rewrite; dfraig; rewrite; dfraig; write_aiger -s ${NAME}.aig" && ~/src/demiurge-1.1.0/tool/build/src/3rd_party/aiger-1.9.4/aigtoaig ${NAME}.aig ${NAME}.aag

rm -rf ${NAME}.mv ${NAME}.aig
