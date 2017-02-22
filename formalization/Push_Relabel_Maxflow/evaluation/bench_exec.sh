#!/bin/bash

for i in "$@"
do
case $i in
    --tests=*)
    tests="${i#*=}"
    shift
    ;;
    --fofu=*)
    platforms_fofu="${i#*=}"
    shift
    ;;
    --prpu=*)
    platforms_prpu="${i#*=}"
    shift
    ;;
    *)
      echo "Unknown command line argument: $i"
      exit 1
    ;;
esac
done


test -n "$tests" || tests=`cat tests`
test -n "$platforms_fofu" || platforms_fofu=`cat fofu-platforms`
test -n "$platforms_prpu" || platforms_prpu=`cat prpu-platforms`

test "$platforms_fofu" = "-" &&  platforms_fofu=""
test "$platforms_prpu" = "-" &&  platforms_prpu=""

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
