#!/bin/bash

for k in `seq 5 5 100` ; do
    ulimit -t 600 -v 4194304 # połowa RAM-u w kB
    echo "k = $k"
    /usr/bin/time -o ${LOG} -f "%e %M" z3 -smt2 hampath_${k}.smt2 >| ./outs/hampath-${k}-z3.out
    LOG="./logs/hampath-${k}-z3.log"
done

