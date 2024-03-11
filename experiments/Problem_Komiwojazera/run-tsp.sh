#!/bin/bash

if [ $# -lt 2 ]; then
    echo "Usage: ./run-tsp.sh graph-name n"
    exit 1
fi
graph=$1
n=$2
LOG="${graph}-${n}.log"
/usr/bin/time -o ${LOG} -f "%e %M" python3 tsp.py \
    "../grafy_wazone/${graph}/${graph}_$n.txt" >| ${graph}-${n}.out
