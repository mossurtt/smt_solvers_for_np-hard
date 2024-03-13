#!/bin/bash

if [ $# -lt 2 ]; then
    echo "Usage: ./run-maxclique.sh graph-name n"
    exit 1
fi
graph=$1
n=$2
LOG="${graph}-${n}.log"
/usr/bin/time -o ${LOG} -f "%e %M" python3 ../maxclique.py \
    "../../grafy_nieskierowane/${graph}/${graph}_$n.txt" >| ${graph}-${n}.out
