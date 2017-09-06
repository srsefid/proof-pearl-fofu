#!/bin/bash

DIRS="Flow_Networks Prpu_Maxflow"
ARCHIVE_NAME="afp-submission.tgz"
AFP="$HOME/devel/isabelle/afp-2016-1-orig"
SESSIONS="Prpu_Maxflow"

EXCLUDE="Prpu_Maxflow/Prpu_Benchmark_Export.thy"


set -e
OLDDIR="$PWD"
TMPDIR=`mktemp -d`
echo "Preparing submission in $TMPDIR"

TGZ_FILE="$OLDDIR/$ARCHIVE_NAME"

# Collect files
cp -a $DIRS "$TMPDIR"

cd "$TMPDIR"

# Clean up
find . -type d -name obsolete | xargs rm -rf
find . -type d -name output | xargs rm -rf
find . -name '*~' | xargs rm -rf

find . -name 'NOTGZ' | xargs rm -rf
find . -name '.gitignore'  | xargs rm -rf

rm -rf $EXCLUDE

# Ughly post-processing
find . -name "ROOT" | xargs sed -i -e '/^ *(\*No-AFP/d'
find . -mindepth 2 -maxdepth 2 -name "*.thy" -or -name "ROOT" | xargs sed -i -e 's|"\$AFP|"..|g'
find . -mindepth 3 -maxdepth 3 -name "*.thy" -or -name "ROOT" | xargs sed -i -e 's|"\$AFP|"../..|g'

# Make tarfile
tar -czf "$TGZ_FILE" $DIRS

cd "$OLDDIR"

# Remove temporary dir
rm -rf "$TMPDIR"

# Setup test
mkdir "$TMPDIR"
cd "$TMPDIR"

# Prepare AFP environment
find "$AFP/thys" -mindepth 1 -maxdepth 1 -type d | xargs -n1 ln -s
cp -a "$AFP/thys/ROOTS" .

# Extract files
tar -xzf "$TGZ_FILE"

# Add new folders to ROOTS
for d in $DIRS; do echo $d >> ROOTS; done

# Test build
isabelle build -d. $SESSIONS

cd $OLDDIR
# rm -rf $TMPDIR
