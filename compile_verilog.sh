#!/bin/bash

vl2mv $1

NAME=${1%.*}

~/src/abc/abc -c "read_blif_mv ${NAME}.mv; strash; refactor; rewrite; dfraig; rewrite; dfraig; write_aiger -s ${NAME}.aig" && ~/src/aiger2termite/aiger/aigtoaig ${NAME}.aig ${NAME}.aag

rm -rf ${NAME}.mv ${NAME}.aig
