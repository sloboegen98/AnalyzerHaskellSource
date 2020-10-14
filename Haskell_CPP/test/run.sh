#!/bin/bash

for t in $(ls in/in*); do
    ./../parsertestexe $t >> /dev/null/
done
