#!/bin/bash

for k in `seq 2 10` ; do
    ulimit -t 600 -v 4194304 # połowa RAM-u w kB
    echo "k = $k"
    LOG="./logs/graphcoloring-${k}-z3.log"
    /usr/bin/time -o ${LOG} -f "%e %M" z3 -smt2 graphcoloring-${k}.smt2 >| ./outs/graphcoloring-${k}-z3.out
done

