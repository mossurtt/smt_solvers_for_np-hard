#!/bin/bash

for k in `seq 5 5 100` ; do
    ulimit -t 600 -v 4194304 # połowa RAM-u w kB
    echo "k = $k"
    /usr/bin/time -o ${LOG} -f "%e %M" yices-smt2 uhampath_${k}.smt2 >| ./outs/uhampath-${k}-yices.out
    LOG="./logs/uhampath-${k}-yices.log"
done

