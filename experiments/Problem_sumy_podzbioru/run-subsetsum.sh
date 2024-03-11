#!/bin/bash

if [ $# -lt 2 ]; then
    echo "Usage: ./run-subsetsum.sh graph-name n"
    exit 1
fi
n=$1
LOG="${n}.log"
/usr/bin/time -o ${LOG} -f "%e %M" python3 subsetsum.py \
    "../zbiory_liczb/$n.txt" >| ${n}.out
