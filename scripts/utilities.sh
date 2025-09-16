#!/bin/bash

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
export pog2smtlib27_dir=$(readlink -f "$SCRIPT_DIR/..")
export pog2smtlib27_test_dir="$pog2smtlib27_dir/test"

#
# tests if two files have equivalent contents (i.e., disregards line breaks and spaces)
#
function files_are_equivalent() {
    f1="$1"
    f2="$2"
    diff -u <(tr -d '[:space:]' < "$f1") <(tr -d '[:space:]' < "$f2") > /dev/null
}
export -f files_are_equivalent

#
# lists all tests where some result output file is equivalent to the reference output file
#
function ls_equivalent() {
    pushd "$pog2smtlib27_test_dir/output/result"
    for file in `ls */output*.smt`
    do
	test=`dirname $file`
	name=`basename $file`
	f1="$test/$name"
	f2="../reference/$test/$name"
	if files_are_equivalent "$f1" "$f2" && ! cmp -s "$f1" "$f2"
	then
	    echo "$test"
	fi
    done
    popd
}
export -f ls_equivalent

#
# lists all tests where some result output file is not equivalent to the reference output file
#
function ls_not_equivalent() {
    pushd "$pog2smtlib27_test_dir/output/result"
    for file in `ls */output*.smt`
    do
	test=`dirname $file`
	name=`basename $file`
	f1="$test/$name"
	f2="../reference/$test/$name"
	if ! files_are_equivalent "$f1" "$f2"
	then
	    echo "$test"
	fi
    done
    popd
}

export -f ls_not_equivalent

#
# replaces reference output files with the result output file, whenever
# - the result output file is equivalent to the reference output file
# - the result output file is not identical to the reference output file
#
function update_references() {
    pushd "$pog2smtlib27_test_dir/output/result"
    for file in `ls */output*.smt`
    do
	test=`dirname $file`
	name=`basename $file`
	f1="$test/$name"
	f2="../reference/$test/$name"
	if files_are_equivalent "$f1" "$f2" && ! cmp -s "$f1" "$f2"
	then
	    cp $f1 $f2
	    echo "$test updated"
	fi
    done
    popd
}

export -f update_references

echo "ls_equivalent        list tests where result is equivalent to reference"
echo "ls_not_equivalent    list tests where result is not equivalent to reference"
echo "update_references    replaces reference with equivalent but not identical result"
echo
echo "pog2smtlib27_dir     $pog2smtlib27_dir"
echo
