#!/bin/bash

if [ $# -lt 1 ]; then
    echo "Usage: ./run-subsetsum.sh n"
    exit 1
fi
n=$1
/usr/bin/time -f "%e %M" python3 subsetsum.py \
    "../zbiory_liczb/$n.txt" >| ./outs/${n}.out
