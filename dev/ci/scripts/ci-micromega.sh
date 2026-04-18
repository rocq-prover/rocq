#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download micromega

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/micromega"
  etc/with-rocq-wrap.sh dune build --root . --only-packages=micromega-plugin @install
  etc/with-rocq-wrap.sh dune install --root . micromega-plugin --prefix="$CI_INSTALL_DIR"
)
