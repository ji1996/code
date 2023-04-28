#!/bin/bash
# for line in `cat D1.list`
# do
#     arr=(${line//,/ })
#     f0=${arr[0]}
#     f1=${arr[1]}
#     solc --abi ./sol/${f0}.sol -o ./abi/${f0}
#     solc --bin ./sol/${f0}.sol -o ./abi/${f0}
# done
# oldIFS=$IFS
# IFS=$'\n'
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
# IFS=$oldIFS
