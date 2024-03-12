#!/bin/bash

for k in `seq 2 10` ; do
    ulimit -t 600 -v 4194304 # połowa RAM-u w kB
    echo "k = $k"
    LOG="./logs/vertexcover-${k}-z3.log"
    /usr/bin/time -o ${LOG} -f "%e %M" cvc5-Linux vertexcover-${n}-${k}.smt2 >| ./outs/vertexcover-${k}-z3.out
done

