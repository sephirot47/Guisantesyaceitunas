#!/bin/bash
#qmake && make clean && make
if [ ! $? == 0 ]; then
	exit -1
fi

for f in inputs/vars*
do
	echo "$f $(/usr/bin/time -f "%U" $(picosat &>/dev/null < $f))"
done
