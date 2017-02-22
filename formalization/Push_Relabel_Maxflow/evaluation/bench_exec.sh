#!/bin/bash

. bench_cmdline.inc

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

  for platform in $platforms_prpu; do
    echo "##### prpu-$platform"
    cd "prpu-$platform"
    ./run $name | tee "$t.$platform.log" | grep "^@@@"
    cd ..
  done
done
