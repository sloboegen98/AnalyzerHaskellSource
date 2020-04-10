#!/bin/bash

function traverse() {
for file in "$1"/*
do
    if [ ! -d "${file}" ]; then
        package="$(cut -d'/' -f2 <<<"${file}")"

        if [[ $file == *.hs ]]; then
            # echo ${file}
            # echo ${package}
            python3 hsparser.py $file $package
        fi

        if [[ $file == *.cabal ]]; then
            # echo ${file}
            echo ${package}
            python3 cblparser.py $file $package
        fi
    else
        echo "Current folder: ${file}"
        traverse "${file}"
    fi
done
}

function main() {
    traverse "$1"
}

main "$1"