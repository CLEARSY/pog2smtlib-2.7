#!/bin/bash

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
export pog2smtlib27_dir=$(readlink -f "$SCRIPT_DIR/..")
export pog2smtlib27_test_dir="$pog2smtlib27_dir/test"

#
# renames all files with suffix .po2 to suffix .smt
#
function mv_po2_suffix() {
    find . -type f -name "*.po2" -exec sh -c 'mv "$1" "${1%.po2}.smt"' _ {} \;
}
export -f mv_po2_suffix

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

function overwrite_references() {
  pushd "$pog2smtlib27_test_dir/output/result"
  for file in `ls */output*.smt`
  do
		test=`dirname $file`
		name=`basename $file`
		f1="$test/$name"
		f2="../reference/$test/$name"
		diff $f1 $f2
		if [ $? -ne 0 ]
		then
	    read -p "overwrite? [y/N] " -n 1 -r
	    echo  # Move to a new line
	    if [[ $REPLY =~ ^[Yy]$ ]]; then
			    cp $f1 $f2
	    fi
		fi
  done
  popd
}

export -f overwrite_references

function run_cvc5() {
    local path="$1"
		local name=`basename $path`
		local prefix=`basename $name .smt`
    local command="$HOME/bin/cvc5 --tlimit=100 ${path}"

		($command > $prefix.stdout 2> $prefix.stderr) 2> /dev/null
		local exit_code=$?

    if [ $exit_code -eq 0 ]; then
        echo -n "$name " && cat $prefix.stdout
    elif [ $exit_code -eq 134 ]; then
        echo "$name timeout"
    else
        echo -n "$name " && cat $prefix.stderr
    fi
}

export -f run_cvc5

echo "mv_po2_suffix        renames files with .po2 suffix to .smt suffix"
echo "ls_equivalent        list tests where result is equivalent to reference"
echo "ls_not_equivalent    list tests where result is not equivalent to reference"
echo "update_references    replaces reference with equivalent but not identical result"
echo
echo "pog2smtlib27_dir     $pog2smtlib27_dir"
echo
echo "run_cvc5"
echo
