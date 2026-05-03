#!/usr/bin/env bash

. ../template/path-init.sh

rm -rf _test
mkdir _test
find . -maxdepth 1 -not -name . -not -name _test -exec cp -r '{}' -t _test ';'

cd _test || exit 1

# recursive expansion
# explicit non-existent file included
actual=`rocq makefile -sources-of .v -o CoqMakefile . nonexistent.v`
expected="a/b/g.v nonexistent.v"
if [ "$actual" != "$expected" ]; then
  echo actual: $actual
  echo expected: $expected
  exit 1
fi

actual=`rocq makefile -sources-of .mli -o CoqMakefile . nonexistent.v`
expected="a/g.mli g.mli"
if [ "$actual" != "$expected" ]; then
  echo actual: $actual
  echo expected: $expected
  exit 1
fi

# expands specific directory, not ., gets the right subset
actual=`rocq makefile -sources-of .mli -o CoqMakefile a`
expected="a/g.mli"
if [ "$actual" != "$expected" ]; then
  echo actual: $actual
  echo expected: $expected
  exit 1
fi

# command line args are in Makefile.conf
rocq makefile -o CoqMakefile . x
actual=`grep "COQMF_CMDLINE_VFILES := . x" CoqMakefile.conf`
if test $? -ne 0; then
  echo bad COQMF_CMDLINE_VFILES:
  grep "COQMF_CMDLINE_VFILES" CoqMakefile.conf
  exit 1
fi
