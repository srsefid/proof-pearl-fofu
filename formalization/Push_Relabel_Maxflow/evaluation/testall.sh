#!/bin/bash

tests=`cat tests`
platforms_fofu=`cat fofu-platforms`
platforms_fifo=`cat fifo-platforms`

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

  for platform in $platforms_fifo; do
    echo "##### fifo-$platform"
    cd "fifo-$platform"
    ./run $name | tee "$t.$platform.log" | grep "^@@@"
    cd ..
  done
done
