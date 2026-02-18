#!/bin/bash
dir="$1"
result=0
counter=0
FILES=$(find "$dir" -type f -name '*.smt')
for file in $FILES; do
  dolmen --input=smt2 --force-smtlib2-logic=ALL "$file"
  if [ $? -ne 0 ]
  then
    echo "Error: $file is not SMTLIB-2.7 compliant."
    result=1
  fi
  counter=$((counter+1))
done
if [ $result -ne 0 ]
then
  echo "Fix the above issues in reference files."
  exit 1
else
  echo "All $counter reference files are SMTLIB-2.7 compliant."
  exit 0
fi
