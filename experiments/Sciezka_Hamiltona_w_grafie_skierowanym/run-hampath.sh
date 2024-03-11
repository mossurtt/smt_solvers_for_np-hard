#!/bin/bash

if [ $# -lt 2 ]; then
    echo "Usage: ./run-hampath.sh graph-name n"
    exit 1
fi
graph=$1
n=$2
LOG="${graph}-${n}.log"
/usr/bin/time -o ${LOG} -f "%e %M" python3 uhampath.py \
    "../grafy_skierowane/${graph}/${graph}_$n.txt" >| ${graph}-${n}.out
