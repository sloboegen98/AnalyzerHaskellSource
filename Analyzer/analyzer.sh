#!/bin/bash

# full_report="full_list.txt"
# report="report.txt"
full_report="$2"
report="$3"

if [ -f $full_report ] ; then
    rm $full_report
fi

if [ -f $report ] ; then
    rm $report
fi

touch $full_report
touch $report

echo "Counting started..."
./counter.sh "$1" $full_report

echo "Process $full_report file..."
python3 process_fl.py $full_report $report

echo "Results in ${report}"