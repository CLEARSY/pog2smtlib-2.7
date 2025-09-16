 #!/bin/bash

testdir="$1"
id="$2"
options="${3:-}"

echo "testdir: $testdir"
echo "id: $id"
echo "options: $options"

cd "$testdir"

. ./setenv.sh

echo "program: $program"

inpdir="$testdir/input/$id"
refdir="$testdir/output/reference/$id"
outdir="$testdir/output/result/$id"
rm -rf "$outdir"
mkdir -p "$outdir"

set -x

$program $options -i "$inpdir/input.pog" -o "$outdir/output" > "$outdir/stdout" 2> "$outdir/stderr"
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

pushd "$outdir"
find . -type f -name "*.po2" -exec sh -c 'mv "$1" "${1%.po2}.smt"' _ {} \;
popd

reffiles=($(find "$refdir" -maxdepth 1 -name "*.smt" -printf "%f\n" | sort))
outfiles=($(find "$outdir" -maxdepth 1 -name "*.smt" -printf "%f\n" | sort))

# Compare lists
if [[ ! "${reffiles[*]}" == "${outfiles[*]}" ]]; then
    echo "Test failed: .smt files differ."
    echo "Reference: ${reffiles[*]}"
    echo "Target:    ${outfiles[*]}"
    exit 1
fi

# Compare contents
for outfile in "$outdir"/*.smt
do
    echo $outfile
    filename=$(basename "$outfile")
    if ! diff "$outfile" "$refdir/$filename" >/dev/null; then
        echo "Error: $filename content differs." >&2
        diff "$outfile" "$refdir/$filename" | tee >(cat 1>&2)
        exit 1
    fi
done

set +x

echo "Test passed $id"
exit 0
