#!/bin/bash

tests=`cat tests`
platforms_fofu=`cat fofu-platforms`
platforms_rtof=`cat rtof-platforms`

tabs -9
echo -ne "Test-Name \t& "
for p in $platforms_fofu; do echo -ne "f-$p\t& "; done
for p in $platforms_rtof; do echo -ne "p-$p\t& "; done

echo ""

for t in $tests; do
  echo -ne "$t\t& "
  for p in $platforms_fofu; do
    log="fofu-$p/$t.$p.log"
    time=`grep "@@@time:" $log | sed -re 's/.*@@@time: //g;s/ms//g'`
    echo -ne "$time\t& "
  done
  
  for p in $platforms_rtof; do
    log="rtof-$p/$t.$p.log"
    time=`grep "@@@time:" $log | sed -re 's/.*@@@time: //g;s/ms//g'`
    echo -ne "$time\t& "
  done

  echo "\\\\"
done

