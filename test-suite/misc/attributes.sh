#!/usr/bin/env bash

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/attributes/

rocq makefile -f _CoqProject -o Makefile

make clean

make src/attribute_plugin.cma

make
