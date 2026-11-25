#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download certirocq

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

# The theories, the plugin extracted with and without optimizations and the C
# runtime, but not the bootstrapped compiler and checker, which take too long.
packages=rocq-certirocq,rocq-certirocq-vanilla

( cd "${CI_BUILD_DIR}/certirocq"
  # compcert is built without native compilation
  for f in theories/dune plugins/plugin/dune plugins/cplugin/dune; do
    grep -q '(mode vo)' "$f" || \
      sed -i -E 's/^\(rocq\.(theory|extraction)$/&\n (mode vo)/' "$f"
  done
  dune build --root . --only-packages="$packages" @install
  dune install --root . --prefix="$CI_INSTALL_DIR" rocq-certirocq rocq-certirocq-vanilla
  # Compile the Wasm test programs with the installed plugin, with the largest
  # stack allowed as it recurses deeply. They are not run, as that needs node,
  # and the C backend is not tested: it follows the word size of CompCert,
  # configured here for a 32 bits target, while the C compiler targets 64 bits.
  ulimit -S -s "$(ulimit -H -s)"
  COQEXTRAFLAGS='-native-compiler no' make -C tests lib
  make -C tests/wasm tests primitive_unit_tests
)
