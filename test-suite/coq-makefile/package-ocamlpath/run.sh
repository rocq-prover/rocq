#!/usr/bin/env bash

set -ex

. ../template/path-init.sh

rm -rf _test
mkdir _test
find . -maxdepth 1 -not -name . -not -name _test -exec cp -r '{}' -t _test ';'
cd _test

touch X.v
rocq c -Q . MyPack X.v
mkdir -p mylib/mypackage/rocq.d/
cp X.vo mylib/mypackage/rocq.d/

rocq makefile -f _CoqProject -o Makefile

make

test -e Foo.vo
