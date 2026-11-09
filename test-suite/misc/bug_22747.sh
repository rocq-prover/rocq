#!/usr/bin/env bash

# Load must not bypass the locality check of custom entries. See #22747.

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/bug_22747/

rocq makefile -f _CoqProject -o Makefile

make clean

if out=$(make theories/A.vo 2>&1); then
    echo "$out"
    make theories/B.vo
    >&2 echo 'Should have failed!'
    exit 1
fi
echo "$out"
echo "$out" | grep -q "has to be declared local"

make theories/Stale.vo
