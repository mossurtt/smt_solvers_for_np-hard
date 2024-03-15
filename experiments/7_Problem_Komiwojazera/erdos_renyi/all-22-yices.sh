#!/bin/bash

if [ "$#" -ne "1" ]; then
    echo "Usage: $0 graph-name"
    exit 1
fi

name=$1
LOG_DIR="./logs"
OUTPUT_LOG="./logs/22-yices.log"

for k in `seq 10 550 560` ; do
    ulimit -t 600
    ulimit -v 8388608 # połowa RAM-u w kB
    echo "k = $k"
    LOG="./${LOG_DIR}/${name}-22-${k}-yices.log"
    /usr/bin/time -o ${LOG} -f "%e %M" yices-smt2 ${name}-22-${k}.smt2 
done

cat ${LOG_DIR}/${name}-22*yices.log | awk '{time+=$1; memory+=$2} END {printf "%.2f %d\n", time, memory}' > $OUTPUT_LOG
