#!/bin/bash

if [ $# -lt 2 ]; then
    echo "Usage: ./run-maxindset.sh graph-name n"
    exit 1
fi
graph=$1
n=$2
/usr/bin/time -f "%e %M" python3 maxindset.py \
    "../grafy_nieskierowane/${graph}/${graph}_$n.txt" 