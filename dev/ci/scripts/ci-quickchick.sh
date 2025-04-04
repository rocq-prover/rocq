#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download quickchick

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/quickchick"
  dune build --root . --only-packages=coq-quickchick @install
  dune install --root . coq-quickchick --prefix=$CI_INSTALL_DIR
)
