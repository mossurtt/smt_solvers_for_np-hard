#!/bin/bash

for n in `seq 5 5 100` ; do
    ulimit -t 600 -v 4194304 # połowa RAM-u w kB
    sh run-hampath.sh barabasi $n
done

