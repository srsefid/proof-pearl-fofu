#!/bin/bash

cd data
./build
cd ..

platforms_fofu=`cat fofu-platforms`
platforms_prpu=`cat prpu-platforms`

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
