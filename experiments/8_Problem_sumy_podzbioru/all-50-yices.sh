#!/bin/bash

LOG_DIR="./logs"
OUTPUT_LOG="./logs/50-yices.log"

for k in `seq 9 2062 10319` ; do
    ulimit -t 600
    ulimit -v 8388608 # połowa RAM-u w kB
    echo "k = $k"
    LOG="./${LOG_DIR}/ss-50-${k}-yices.log"
    /usr/bin/time -o ${LOG} -f "%e %M" yices-smt2 subsetsum-50-${k}.smt2 
done

cat ${LOG_DIR}/ss-50*yices.log | awk '{time+=$1; memory+=$2} END {printf "%.2f %d\n", time, memory}' > $OUTPUT_LOG

rm -f ${LOG_DIR}/ss-50*yices.log
