#!/bin/bash

# program = $1

mkdir -p result

for t in $(ls test/in/in*); do
    num=${t#"test/in/in"}
    out="test/out/out"$num
    ans="result/ans"$num

    ./parsertestexe $t >$ans

    if cmp $ans $out; then
        echo "Ok: $t"
        rm $ans
    else 
        echo "WA:$t"
    fi
done