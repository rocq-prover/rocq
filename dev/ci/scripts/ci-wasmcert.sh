#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download wasmcert

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/wasmcert"
  # We only build the theory: the extracted interpreter in src/ belongs to the
  # same package but needs the wasm opam package, which is not in the CI image.
  rm -rf src
  # compcert is built without native compilation
  grep -q '(mode vo)' theories/dune || \
    sed -i -E 's/^\(coq\.theory$/&\n  (mode vo)/' theories/dune
  dune build --root . --only-packages=coq-wasm @install
  dune install --root . coq-wasm --prefix="$CI_INSTALL_DIR"
)
