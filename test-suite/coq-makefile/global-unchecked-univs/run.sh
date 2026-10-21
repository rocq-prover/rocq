#!/usr/bin/env bash

. ../template/path-init.sh

rm -rf _test
mkdir _test
find . -maxdepth 1 -not -name . -not -name _test -exec cp -r '{}' -t _test ';'
cd _test

rocq makefile -f _CoqProject -o Makefile

# loading flags not supported by separate native compiler;
# the test declares global universes, as in the rest of the test-suite universe polymorphism is off
export COQEXTRAFLAGS='-native-compiler no -unset "Universe Polymorphism"'
make
