#!/bin/bash

BASEDIR=$PWD

REBUILD=false
UPLOAD=false

while [[ $# -gt 0 ]]
do
key="$1"

case $key in
    -r|--rebuild)
    REBUILD=true
    ;;
    -u|--upload)
    UPLOAD=true
    ;;
    *)
    echo "Unknown command line argument $1"        # unknown option
    exit 1
    ;;
esac
shift # past argument or value
done



if $REBUILD; then

cd formalization
isabelle build -b -d '$AFP' -D .
./mkpkg.sh
cd $BASEDIR

fi


rm -rf html
mkdir -p html


cp -a README.md html/
cp -a formalization/maxflow.tgz html/


cp formalization/Flow_Networks/output/outline.pdf  html/fnet_outline.pdf
cp formalization/Flow_Networks/output/document.pdf html/fnet_document.pdf

cp formalization/Edka_Maxflow/output/outline.pdf  html/edka_outline.pdf
cp formalization/Edka_Maxflow/output/document.pdf html/edka_document.pdf

cp formalization/Prpu_Maxflow/output/outline.pdf  html/prpu_outline.pdf
cp formalization/Prpu_Maxflow/output/document.pdf html/prpu_document.pdf


pandoc -V pagetitle="Formalization of Network Flow Algorithms" -s index.md > html/index.html


if $UPLOAD; then
  LOCAL_DEST=~/devel/www21-lammich/max_flow
  rm -rf $LOCAL_DEST
  cp -a html $LOCAL_DEST
  cd $LOCAL_DEST
  hg add .
  hg commit -m "Automatic update of Maxflow" .
  hg push
  cd $BASEDIR
fi


