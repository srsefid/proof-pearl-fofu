#!/bin/bash

. bench_cmdline.inc


test -t 1 && tabs 18,+10,+10,+10,+10,+10,+10,+10,+10,+10,+10,+10,+10,+10,+10,+10,+10,+10,+10,+10,+10,+10

echo -ne "Name \t, "
for p in $platforms_fofu; do echo -ne "f-$p\t, "; done
for p in $platforms_prpu; do echo -ne "p-$p\t, "; done

echo ""

tests=$(for t in $fofu_tests $prpu_tests; do echo $t; done | awk '!a[$0]++')

for t in $tests; do
  echo -ne "$t\t, "
  for p in $platforms_fofu; do
    log="fofu-$p/$t.$p.log"
    
    if test -f $log; then
      time=`grep "@@@time:" $log | sed -re 's/.*@@@time: //g;s/ms//g'`
    else
      time="---"
    fi
    echo -ne "$time\t, "
  done
  
  for p in $platforms_prpu; do
    log="prpu-$p/$t.$p.log"
    if test -f $log; then
      time=`grep "@@@time:" $log | sed -re 's/.*@@@time: //g;s/ms//g'`
    else
      time="---"
    fi
    echo -ne "$time\t, "
  done

  echo ""
done

