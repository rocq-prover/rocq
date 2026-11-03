#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download proofgeneral

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi


( cd "${CI_BUILD_DIR}/proofgeneral"
  make tests
  make -C ci/compile-tests test
  make -C ci/simple-tests coq-all
)
