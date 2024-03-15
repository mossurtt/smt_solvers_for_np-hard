#!/bin/bash

for n in `seq 5 5 55` ; do
    ulimit -t 600
    ulimit -v 8388608 # połowa RAM-u w kB
    sh run-subsetsum.sh $n
done

