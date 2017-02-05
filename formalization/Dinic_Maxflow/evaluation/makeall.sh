#!/bin/bash

cd data
./build
cd ..

platforms_fofu=`cat fofu-platforms`
platforms_rtof=`cat rtof-platforms`

for p in $platforms_fofu; do
  echo "Compiling fofu-$p"
  cd "fofu-$p"
  ./build
  cd ..
done

for p in $platforms_rtof; do
  echo "Compiling rtof-$p"
  cd "rtof-$p"
  ./build
  cd ..
done
