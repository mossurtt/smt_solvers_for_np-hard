#!/bin/bash

if [ "$#" -ne "1" ]; then
    echo "Usage: $0 graph-name"
    exit 1
fi

name=$1

for n in `seq 4 2 24` ; do
    ulimit -t 600 
    ulimit -v 8388608 # połowa RAM-u w kB
    LOG="./logs/${name}-${n}-yices.log"
    /usr/bin/time -o ${LOG} -f "%e %M" yices-smt2 ${name}_${n}.smt2 
done
