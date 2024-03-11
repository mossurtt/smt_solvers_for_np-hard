#!/bin/bash

for k in `seq 2 10` ; do
    ulimit -t 600 -v 4194304 # połowa RAM-u w kB
    echo "k = $k"
    /usr/bin/time -f "%e %M" cvc5 maxclique-10-${k}.smt2
done

