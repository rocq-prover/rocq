#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/elpi"
  touch dune-workspace # we don't call dune directly so can't pass --root .
  make -j1 all-tests-no-plugins
  make -j1 all-examples
)
