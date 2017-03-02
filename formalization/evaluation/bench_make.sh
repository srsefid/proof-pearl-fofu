#!/bin/bash

. bench_cmdline.inc

cd data
./build
cd ..

for p in $platforms_fofu; do
  echo "Compiling fofu-$p"
  cd "fofu-$p"
  ./build
  cd ..
done

for p in $platforms_prpu; do
  echo "Compiling prpu-$p"
  cd "prpu-$p"
  ./build
  cd ..
done
