#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download trakt

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/trakt"
  dune build --root . --only-packages=rocq-trakt @install
  dune install --root . rocq-trakt --prefix="$CI_INSTALL_DIR"
)
