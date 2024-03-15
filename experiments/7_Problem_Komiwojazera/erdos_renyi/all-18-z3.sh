#!/bin/bash

if [ "$#" -ne "1" ]; then
    echo "Usage: $0 graph-name"
    exit 1
fi

name=$1
LOG_DIR="./logs"
OUTPUT_LOG="./logs/18-z3.log"

for k in `seq 10 383 393` ; do
    ulimit -t 600
    ulimit -v 8388608 # połowa RAM-u w kB
    echo "k = $k"
    LOG="./${LOG_DIR}/${name}-18-${k}-z3.log"
    /usr/bin/time -o ${LOG} -f "%e %M" z3 -smt2 ${name}-18-${k}.smt2 
done

cat ${LOG_DIR}/${name}-18*z3.log | awk '{time+=$1; memory+=$2} END {printf "%.2f %d\n", time, memory}' > $OUTPUT_LOG
