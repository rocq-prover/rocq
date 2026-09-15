#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

WITH_SUBMODULES=1 # force git for LFS dumps used in tests
git_download lean_importer

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

export COQEXTRAFLAGS='-native-compiler no'

( cd "${CI_BUILD_DIR}/lean_importer"
  make .merlin
  make
  make test
)
