#!/bin/bash

LOG_DIR="./logs"
OUTPUT_LOG="./logs/45-cvc5.log"

for k in `seq 1 1709 8546` ; do
    ulimit -t 600
    ulimit -v 8388608 # połowa RAM-u w kB
    echo "k = $k"
    LOG="./${LOG_DIR}/ss-45-${k}-cvc5.log"
    /usr/bin/time -o ${LOG} -f "%e %M" cvc5-Linux subsetsum-45-${k}.smt2 
done

cat ${LOG_DIR}/ss-45*cvc5.log | awk '{time+=$1; memory+=$2} END {printf "%.2f %d\n", time, memory}' > $OUTPUT_LOG

rm -f ${LOG_DIR}/ss-45*cvc5.log
