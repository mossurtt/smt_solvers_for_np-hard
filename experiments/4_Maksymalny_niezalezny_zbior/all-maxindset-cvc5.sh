#!/bin/bash

for k in `seq 2 10` ; do
    ulimit -t 600 -v 4194304 # połowa RAM-u w kB
    echo "k = $k"
    LOG="./logs/maxindset-${k}-cvc5.log"
    /usr/bin/time -o ${LOG} -f "%e %M" cvc5-Linux maxindset-${k}.smt2 >| ./outs/maxindset-${k}-cvc5.out
done

