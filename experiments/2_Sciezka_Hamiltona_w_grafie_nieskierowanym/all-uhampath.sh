#!/bin/bash

for n in `seq 5 5 30` ; do
    ulimit -t 600 -v 4194304 # połowa RAM-u w kB
    sh run-uhampath.sh barabasi $n
done

