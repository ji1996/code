#!/bin/bash
prev_line=""
prev_row=""
for line in `cat cve.list`
do
    arr=(${line//,/ })
    f=${arr[0]}
    if [ "$prev_line" = "" ]; then
        prev_line="$f"
        prev_row="$line"
    else
        if [ "$f" = "$prev_line" ]; then
            prev_line="$f"
            prev_row="$line"
        else
            echo $prev_row >> new.list
            prev_line="$f"
            prev_row="$line"
        fi
    fi
done
