
for i in "$@"
do
case $i in
    --tests=*)
    fofu_tests="${i#*=}"
    prpu_tests="${i#*=}"
    shift
    ;;
    --fofu-tests=*)
    fofu_tests="${i#*=}"
    shift
    ;;
    --prpu-tests=*)
    prpu_tests="${i#*=}"
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


test -n "$fofu_tests" || fofu_tests=`cat fofu-tests`
test -n "$prpu_tests" || prpu_tests=`cat prpu-tests`
test -n "$platforms_fofu" || platforms_fofu=`cat fofu-platforms`
test -n "$platforms_prpu" || platforms_prpu=`cat prpu-platforms`

test "$platforms_fofu" = "-" &&  platforms_fofu=""
test "$platforms_prpu" = "-" &&  platforms_prpu=""

