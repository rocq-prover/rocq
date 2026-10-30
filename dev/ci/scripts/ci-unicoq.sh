#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download unicoq

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/unicoq"
  dune build --root . --only-packages=coq-unicoq @install @runtest
  dune install --root . coq-unicoq --prefix="$CI_INSTALL_DIR"
)
