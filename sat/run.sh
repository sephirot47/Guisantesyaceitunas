#!/bin/bash
#qmake && make clean && make
if [ ! $? == 0 ]; then
	exit -1
fi

for f in inputs/vars-25*
do
	echo -e "$f:\t"
	./sat < $f
done
