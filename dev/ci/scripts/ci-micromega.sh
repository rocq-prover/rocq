#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download micromega

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/micromega"
  dune build --root . --only-packages=rocq-micromega-plugin @install
  dune install --root . rocq-micromega-plugin --prefix=$CI_INSTALL_DIR
)
