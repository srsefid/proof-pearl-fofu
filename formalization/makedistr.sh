#!/bin/bash

echo 'Collecting'
# Collect theory files
THYS=`isabelle build -d. -nl Edka | egrep '^ +[^/ ]'`

# Collect root files
ROOTS=""
function follow_roots {
  local DIR="$1"
  
  if test -f "$DIR/ROOT"; then
    ROOTS="$ROOTS $DIR/ROOT"
  fi
  if test -f "$DIR/ROOTS"; then
    ROOTS="$ROOTS $DIR/ROOTS"
    for r in `cat $DIR/ROOTS`; do
      local ND="$DIR/$r"
      [[ "$r" != '.' ]] && follow_roots "$ND"
    done  
  fi
}

follow_roots "."


# Collect extra files

EXTRA=""
EXTRA="$EXTRA `find evaluation -type f -not -name '*~' -not -path '*/samples/*' -not -name '*.log' -not -name '*.class'`"
EXTRA="$EXTRA README.md"

FILES="$THYS $ROOTS $EXTRA"

OUTNAME="edmonds_karp.tgz"

echo 'Making archive'
tar --transform 's,^\./,,;s,^,edmonds_karp/,' -czf $OUTNAME $FILES

cp $OUTNAME html
