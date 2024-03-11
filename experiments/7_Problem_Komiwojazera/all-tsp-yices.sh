#!/bin/bash

for k in `seq 2 10` ; do
    ulimit -t 600 -v 4194304 # połowa RAM-u w kB
    echo "k = $k"
    LOG="./logs/tsp-${k}-yices.log"
    /usr/bin/time -o ${LOG} -f "%e %M" yices-smt2 -smt2 tsp-${k}.smt2 >| ./outs/tsp-${k}-yices.out
done

