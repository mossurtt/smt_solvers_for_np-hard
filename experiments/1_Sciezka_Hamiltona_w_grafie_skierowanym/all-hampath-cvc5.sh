#!/bin/bash

for k in `seq 5 5 100` ; do
    ulimit -t 600 -v 4194304 # połowa RAM-u w kB
    echo "k = $k"
    /usr/bin/time -o ${LOG} -f "%e %M" cvc5-Linux hampath_${k}.smt2 >| ./outs/hampath-${k}-cvc5.out
    LOG="./logs/hampath-${k}-cvc5.log"
done

