#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

root=$PWD

make doc/unreleased.rst

mkdir -p "$CI_BUILD_DIR/refman"
cd "$CI_BUILD_DIR/refman"

export ROCQRST_EXTRA=all
export PYTHONPATH="$root/_build/default/config:$root/doc/tools:$PYTHONPATH"

sphinx-build -q -W -b html "$root/doc/sphinx" -j "$NJOBS" refman-html

sphinx-build -q -W -b latex "$root/doc/sphinx" -j "$NJOBS" refman-pdf
make -C refman-pdf LATEXMKOPTS=-silent
