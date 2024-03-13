#!/bin/bash

if [ "$#" -ne "1" ]; then
    echo "Usage: $0 graph-name"
    exit 1
fi

name=$1
for k in `seq 2 6` ; do
    ulimit -t 600 -v 8388608 # połowa RAM-u w kB
    echo "k = $k"
    LOG="./logs/${name}-8-${k}-cvc5.log"
    /usr/bin/time -o ${LOG} -f "%e %M" cvc5-Linux ${name}-8-${k}.smt2 >| ./outs/${name}-8-${k}-cvc5.out
done

