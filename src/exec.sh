#! /bin/bash

domain=$1;
file=$2;
trace=$3;
cat $file;
./analyzer.byte -$domain -trace $file 
