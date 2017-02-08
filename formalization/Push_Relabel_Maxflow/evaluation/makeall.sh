#!/bin/bash

cd data
./build
cd ..

platforms_fofu=`cat fofu-platforms`
platforms_fifo=`cat fifo-platforms`

for p in $platforms_fofu; do
  echo "Compiling fofu-$p"
  cd "fofu-$p"
  ./build
  cd ..
done

for p in $platforms_fifo; do
  echo "Compiling fifo-$p"
  cd "fifo-$p"
  ./build
  cd ..
done
