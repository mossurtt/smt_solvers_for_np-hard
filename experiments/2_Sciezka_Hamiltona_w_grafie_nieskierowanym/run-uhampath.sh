#!/bin/bash

if [ $# -lt 2 ]; then
    echo "Usage: ./run-uhampath.sh graph-name n"
    exit 1
fi
graph=$1
n=$2
LOG="./logs/${graph}-${n}.log"
/usr/bin/time -o ${LOG} -f "%e %M" python3 uhampath.py \
    "../grafy_nieskierowane/${graph}/${graph}_$n.txt" >| ./outs/${graph}-${n}.out
