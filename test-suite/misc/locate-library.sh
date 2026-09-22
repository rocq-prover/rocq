#!/bin/sh

# Locate Library prints an absolute path, so this cannot be an output test.

set -e

rm -rf misc/locate-library/
mkdir misc/locate-library

echo 'Locate Library TestSuite.admit.' > misc/locate-library/main.v

$coqc misc/locate-library/main.v > misc/locate-library/out 2>&1
cat misc/locate-library/out
grep -q 'TestSuite.admit is bound to file' misc/locate-library/out
