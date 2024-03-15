#!/bin/bash

LOG_DIR="./logs"
OUTPUT_LOG="./logs/25-yices.log"

for k in `seq 6 526 2636` ; do
    ulimit -t 600
    ulimit -v 8388608 # połowa RAM-u w kB
    echo "k = $k"
    LOG="./${LOG_DIR}/ss-25-${k}-yices.log"
    /usr/bin/time -o ${LOG} -f "%e %M" yices-smt2 subsetsum-25-${k}.smt2 
done

cat ${LOG_DIR}/ss-25*yices.log | awk '{time+=$1; memory+=$2} END {printf "%.2f %d\n", time, memory}' > $OUTPUT_LOG

rm -f ${LOG_DIR}/ss-25*yices.log
