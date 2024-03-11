#!/bin/bash

for k in `seq 2 10` ; do
    ulimit -t 600 -v 4194304 # połowa RAM-u w kB
    echo "k = $k"
    LOG="./logs/${k}-cvc5.log"
    /usr/bin/time -o ${LOG} -f "%e %M" cvc5-Linux subsetsum-${k}.smt2 >| ./outs/${k}-cvc5.out
done

