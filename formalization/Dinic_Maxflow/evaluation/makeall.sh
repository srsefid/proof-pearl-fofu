#!/bin/bash

cd data
./build
cd ..

platforms=`cat platforms`

for p in $platforms; do
  echo "Compiling $p"
  cd "fofu-$p"
  ./build
  cd ..
done

echo "Compiling Rtof-SML"
cd "rtof-SML"
./build
cd ..
