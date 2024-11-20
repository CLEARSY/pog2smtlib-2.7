#!/bin/bash

function INSERT_LICENSE_IN_SOURCE_FILES () {
for i in `find src/B2SMTLIB \( -iname \*.cpp -o -iname \*.h \) -print`
do
  if ! grep -q Copyright $i
  then
    cat header.txt $i >$i.new && mv $i.new $i
  fi
done

for i in `find src/POGLoader \( -iname \*.cpp -o -iname \*.h \) -print`
do
  if ! grep -q Copyright $i
  then
    cat header.txt $i >$i.new && mv $i.new $i
  fi
done
}

export -f INSERT_LICENSE_IN_SOURCE_FILES
