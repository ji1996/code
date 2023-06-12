#!/bin/bash
for file in ./sol/*
do
    f=`basename ${file} .sol`
    # contract=""
    # echo ${f} >> done.list
    cat $file | while read row
    do
        arr=(${row})
        if [ "${arr[0]}" = "contract" ]; then
            contract=${arr[1]}
            echo ${f},${contract} >> cve.list
            	# echo ${f} >> RE.list
        fi
    done
done
