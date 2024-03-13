#!/bin/bash

if [ "$#" -ne "1" ]; then
    echo "Usage: $0 graph-name"
    exit 1
fi

name=$1
for k in `seq 2 10` ; do
    ulimit -t 600 -v 8388608 # połowa RAM-u w kB
    echo "k = $k"
    LOG="./logs/${name}-16-${k}-yices.log"
    /usr/bin/time -o ${LOG} -f "%e %M" yices-smt2 ${name}-16-${k}.smt2 >| ./outs/${name}-16-${k}-yices.out
done

