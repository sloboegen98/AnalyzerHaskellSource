#! /bin/bash

program = $1

mkdir -p result

for t in $(ls test/in/*); do
    num = ${t#"test/in/in"}
    out = "test/out/out"$num
    ans = "result/ans"$num

    $(program) <$t >$ans

    if cmp -s $ans $out; then
        echo "Ok: $t"
        rm $ans
    else 
        echo "WA:$t"
    fi
done