#!/bin/bash

for k in `seq 2 6` ; do
    ulimit -t 600 -v 4194304 # połowa RAM-u w kB
    echo "k = $k"
    /usr/bin/time -f "%e %M" z3 -smt2 barabasi_15_${k}.smt2
done

