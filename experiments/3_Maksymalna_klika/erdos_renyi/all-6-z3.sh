#!/bin/bash

if [ "$#" -ne "1" ]; then
    echo "Usage: $0 graph-name"
    exit 1
fi

name=$1
for k in `seq 2 4` ; do
    ulimit -t 600
    ulimit -v 8388608 # połowa RAM-u w kB
    echo "k = $k"
    LOG="./logs/${name}-6-${k}-z3.log"
    /usr/bin/time -o ${LOG} -f "%e %M" z3 -smt2 ${name}-6-${k}.smt2 >| ./outs/${name}-6-${k}-z3.out
done

