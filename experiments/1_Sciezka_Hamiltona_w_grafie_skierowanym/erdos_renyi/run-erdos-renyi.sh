#!/bin/bash

if [ $# -lt 2 ]; then
    echo "Usage: ./run-erdos-renyi.sh graph-name n"
    exit 1
fi
graph=$1
n=$2
/usr/bin/time -f "%e %M" python3 ../hampath.py \
    "../../grafy_skierowane/${graph}/${graph}_$n.txt" >| ./outs/${graph}-${n}.out
