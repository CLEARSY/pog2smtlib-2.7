 #!/bin/bash

testdir="$1"
id="$2"

echo "testdir: $testdir"
echo "id: $id"

set -x

cd "$testdir"

. ./setenv.sh

echo "program: $program"

inpdir="$testdir/input/$id"
refdir="$testdir/output/reference/$id"
outdir="$testdir/output/result/$id"
rm -rf "$outdir"
mkdir -p "$outdir"

$program -i "$inpdir/input.pog" -o "$outdir/output.pog" > "$outdir/stdout" 2> "$outdir/stderr"
echo $? > "$outdir/exitcode"

diff "$outdir/stdout" "$refdir/stdout"
if [ $? -ne 0 ]; then
    echo "Test failed: stdout differs"
    exit 1
fi

diff "$outdir/stderr" "$refdir/stderr"
if [ $? -ne 0 ]; then
    echo "Test failed: stderr differs"
    exit 1
fi

diff "$outdir/exitcode" "$refdir/exitcode"
if [ $? -ne 0 ]; then
    echo "Test failed: exitcode differs"
    exit 1
fi

diff "$outdir/output_0_0.po2" "$refdir/output.smt"
if [ $? -ne 0 ]; then
    echo "Test failed: produced SMT differs"
    exit 1
fi

echo "Test passed"
exit 0
