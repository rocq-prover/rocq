#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download certirocq

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/certirocq"
  # compcert is built without native compilation, so neither are the theories, nor
  # the files that the tests and the bootstrap compile with rocq c
  for f in $(grep -rlE --include=dune --exclude-dir=_build '^\(rocq\.(theory|extraction)$' .); do
    grep -q '(mode vo)' "$f" || \
      sed -i -E 's/^\(rocq\.(theory|extraction)$/&\n (mode vo)/' "$f"
  done
  sed -i '/-native-compiler no/!s/rocq c /rocq c -native-compiler no /' \
    tests/*/dune bootstrap/*/dune
  # The C backend takes the size of words from CompCert, configured here for a 32
  # bits target, while the C compiler, the runtime, and the OCaml plugins that the
  # bootstrapped compiler and checker are linked into are 64 bits: the plugins are
  # extracted for 64 bits words (Archi.ptr64 is the only parameter of the target
  # that the generated C depends on).
  for f in plugins/plugin/extraction.v plugins/cplugin/extraction.v; do
    grep -q 'Archi.ptr64' "$f" || \
      sed -i '0,/^Separate Extraction/s//Extract Inlined Constant Archi.ptr64 => "true".\n&/' "$f"
  done
  # The theories of the compiler, without its proofs, the plugins and the runtime
  dune build --root . @@compiler
  # The tests, which use the plugins from the build directory, and the bootstrapped
  # compiler and checker. The Wasm tests are left out, as running them needs node.
  dune test --root . tests/programs tests/closures tests/axioms tests/ffi tests/ocaml bootstrap
)
