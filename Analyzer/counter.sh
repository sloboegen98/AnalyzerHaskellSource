#!/bin/bash

full_report="$2"

function traverse() {
for file in "$1"/*
do
    if [ ! -d "${file}" ]; then
        package="$(cut -d'/' -f3 <<<"${file}")"

        if [[ $file == *.hs ]]; then
            # echo ${file}
            # echo ${package}
            python3 hsparser.py $file $package $full_report
        fi

        if [[ $file == *.cabal ]]; then
            # echo ${file}
            echo ${package}
            python3 cblparser.py $file $package $full_report
        fi
    else
        # echo "Current folder: ${file}"
        traverse "${file}"
    fi
done
}

function main() {
    traverse "$1"
}

main "$1"
