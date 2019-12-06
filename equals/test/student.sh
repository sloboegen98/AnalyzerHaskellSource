#!/bin/bash

#script to recursively travel a dir of n levels

function traverse() {
for file in "$1"/*
do
    if [ ! -d "${file}" ] ; then
        echo ${file} >> student.txt
        cat ${file} >> student.txt
        echo >> student.txt 
        ./../parsertestexe $file >> student.txt
        echo "------------------------" >> student.txt
        echo >> student.txt
    else
        echo "entering recursion with: ${file}"
        traverse "${file}"
    fi
done
}

function main() {
    traverse "$1"
}

main "$1"