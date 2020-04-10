#!/bin/bash

full_report="full_list.txt"
report="report.txt"

if [ -f $full_report ] ; then
    rm $full_report
fi

if [ -f $report ] ; then
    rm $report
fi

touch full_text.txt
touch report.txt

echo "Counting started..."
./counter.sh "$1"

echo "Process $full_report.txt file..."
python3 process_fl.py

echo "Results in report.txt"