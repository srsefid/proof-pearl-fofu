#!/bin/bash

tests=`cat tests`
platforms_fofu=`cat fofu-platforms`
platforms_rtof=`cat rtof-platforms`

for t in $tests; do
  echo "*********************"
  echo "$t"
  echo "*********************"

  name="../data/samples/g-$t.txt"

  for platform in $platforms_fofu; do
    echo "##### fofu-$platform"
    cd "fofu-$platform"
    ./run $name | tee "$t.$platform.log" | grep "^@@@"
    cd ..
  done

  for platform in $platforms_rtof; do
    echo "##### rtof-$platform"
    cd "rtof-$platform"
    ./run $name | tee "$t.$platform.log" | grep "^@@@"
    cd ..
  done
done
