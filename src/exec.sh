#! /bin/bash

domain=$1;
file=$2;
trace=$3;
cat -n $file;
./analyzer.byte -$domain -trace $file 
