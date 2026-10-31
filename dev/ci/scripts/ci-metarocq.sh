#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download metarocq

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/metarocq"
  if [ -e dune-project ]; then
    # @runtest builds the test-suite and the examples
    dune build --root . @install @runtest
    dune install --root . --prefix="$CI_INSTALL_DIR"
  else
    export COQEXTRAFLAGS='-native-compiler no -w -rewrite-rw'
    [ -e pcuic/metarocq-config ] || ./configure.sh local
    make template-rocq TIMED=pretty-timed
    make all TIMED=pretty-timed
    make test-suite TIMED=pretty-timed
    make install
  fi
)
