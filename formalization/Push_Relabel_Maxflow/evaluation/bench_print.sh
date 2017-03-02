#!/bin/bash

. bench_cmdline.inc

tabs -9
echo -ne "Name \t& "
for p in $platforms_fofu; do echo -ne "f-$p\t& "; done
for p in $platforms_prpu; do echo -ne "p-$p\t& "; done

echo ""

for t in $tests; do
  echo -ne "$t\t& "
  for p in $platforms_fofu; do
    log="fofu-$p/$t.$p.log"
    time="-1"
    if [ -e $log ]; then
      if [ -n "$(grep "@@@time:" $log)" ]; then
        time=`grep "@@@time:" $log | sed -re 's/.*@@@time: //g;s/ms//g'`
      fi
    fi    
    echo -ne "$time\t& "
  done
  
  for p in $platforms_prpu; do
    log="prpu-$p/$t.$p.log"
    time="-1"
    if [ -e $log ]; then
      if [ -n "$(grep "@@@time:" $log)" ]; then
        time=`grep "@@@time:" $log | sed -re 's/.*@@@time: //g;s/ms//g'`
      fi
    fi 
    echo -ne "$time\t& "
  done

  echo "\\\\"
done

