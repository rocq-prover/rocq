#!/usr/bin/env bash

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/attributes/

rm -rf _test
mkdir _test
find . -maxdepth 1 -not -name . -not -name _test -exec cp -r '{}' -t _test ';'
cd _test

rocq makefile -f _CoqProject -o Makefile

make

if ! [ -e theories/attr.vo ]; then
  >&2 echo Missing attr.vo after successful compilation
  exit 1
fi

# Check the messages emitted by the #[print] and #[error] attribute hooks.
rocq c -q -Q theories Attributes -I src theories/attr.v > attr.out.real 2>&1
diff -u --strip-trailing-cr ../attr.out attr.out.real
