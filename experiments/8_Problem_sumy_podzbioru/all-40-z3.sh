#!/bin/bash

LOG_DIR="./logs"
OUTPUT_LOG="./logs/40-z3.log"

for k in `seq 29 1287 6464` ; do
    ulimit -t 600
    ulimit -v 8388608 # połowa RAM-u w kB
    echo "k = $k"
    LOG="./${LOG_DIR}/ss-40-${k}-z3.log"
    /usr/bin/time -o ${LOG} -f "%e %M" z3 -smt2 subsetsum-40-${k}.smt2 
done

cat ${LOG_DIR}/ss-40*z3.log | awk '{time+=$1; memory+=$2} END {printf "%.2f %d\n", time, memory}' > $OUTPUT_LOG

rm -f ${LOG_DIR}/ss-40*z3.log
