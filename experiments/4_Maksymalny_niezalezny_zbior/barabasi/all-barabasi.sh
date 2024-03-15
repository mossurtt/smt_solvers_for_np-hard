#!/bin/bash

for n in `seq 4 2 24` ; do
    ulimit -t 600 
    ulimit -v 8388608 # połowa RAM-u w kB
    sh run-maxindset.sh barabasi $n
done

