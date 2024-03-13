#!/bin/bash

for n in `seq 4 2 24` ; do
    ulimit -t 600 
    ulimit -v 4194304 # połowa RAM-u w kB
    sh run-erdos-renyi.sh erdos-renyi $n
done

