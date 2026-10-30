#!/usr/bin/env bash

set -e

export COQBIN="$BIN"
export PATH="$BIN:$PATH"

cd misc/unsafe-casts
rocq makefile -f _CoqProject -o Makefile
make clean
make unsafe_cast_plugin.cmxs

rocq compile -q -test-mode -R . UnsafeCasts -I . Main.v > main.out 2>&1
diff -u --strip-trailing-cr main.out.reference main.out
rocq compile -q -test-mode -R . UnsafeCasts -I . Erasure.v > erasure.out 2>&1
diff -u --strip-trailing-cr erasure.out.reference erasure.out
rocq compile -q -test-mode -R . UnsafeCasts -I . Imported.v > imported.out 2>&1
diff -u --strip-trailing-cr imported.out.reference imported.out
rocq compile -q -test-mode -async-proofs on -async-proofs-j 2 \
  -R . UnsafeCasts -I . Async.v > async.out 2>&1
diff -u --strip-trailing-cr async.out.reference async.out

# The standalone checker validates the serialized payload, but must reject
# unsafe casts when their checking plugin is not registered in that process.
if "${BIN}rocqchk" -silent -R . UnsafeCasts UnsafeCasts.Imported > checker.out 2>&1; then
  echo "rocqchk unexpectedly accepted an unregistered unsafe cast"
  exit 1
fi
grep -q 'Unsafe cast .* is not registered' checker.out

# Regressions for review findings #1-3. Collect failures so that one bug does
# not hide the other reproductions. The references describe fixed behavior;
# these checks intentionally fail until the implementation is repaired.
regression_failures=0

check_unregistered_library () {
  local library="$1"
  if ! rocq compile -q -test-mode -R . UnsafeCasts -I . "$library.v" \
      > "$library.out" 2>&1; then
    echo "FAIL #1: could not compile $library.v (see $library.out)"
    return 1
  fi
  if "${BIN}rocqchk" -silent -R . UnsafeCasts "UnsafeCasts.$library" \
      > "$library-checker.out" 2>&1; then
    echo "FAIL #1: rocqchk accepted UnsafeCasts.$library without its cast plugin"
    return 1
  fi
  if ! grep -Fq 'Unsafe cast "test.accept" is not registered.' "$library-checker.out"; then
    echo "FAIL #1: $library failed for an unexpected reason (see $library-checker.out)"
    return 1
  fi
}

# Exercise the checker API with registered handlers too: refusing all unsafe
# casts, or only checking registration without running the callback, is wrong.
check_original_inductive_casts () {
  if ! "${OCAMLFIND:-ocamlfind}" ocamlopt -rectypes -linkpkg \
      -package rocq-runtime.checklib checker_cast_test.ml -o checker_cast_test.exe; then
    echo "FAIL #1: could not build the original-inductive-cast checker test"
    return 1
  fi
  if ! ./checker_cast_test.exe; then
    echo "FAIL #1: original inductive casts were not independently checked"
    return 1
  fi
}

check_relevance () {
  if ! rocq compile -q -test-mode -R . UnsafeCasts -I . Relevance.v \
      > relevance.out 2>&1; then
    echo "FAIL #2: relevance checks or metadata invariants failed (see relevance.out)"
    return 1
  fi
  if ! rocq compile -q -test-mode -R . UnsafeCasts -I . ImportedRelevance.v \
      > imported-relevance.out 2>&1; then
    echo "FAIL #2: serialized relevance metadata is inconsistent (see imported-relevance.out)"
    return 1
  fi
}

check_sealed_interfaces () {
  local library="$1"
  if ! rocq compile -q -test-mode -R . UnsafeCasts -I . "$library.v" \
      > "$library.out" 2>&1; then
    echo "FAIL #3: could not compile $library.v (see $library.out)"
    return 1
  fi
  if ! diff -u --strip-trailing-cr sealed-interfaces.out.reference "$library.out"; then
    echo "FAIL #3: $library lost exposed-interface assumptions"
    return 1
  fi
}

run_regression () {
  if "$@"; then
    :
  else
    regression_failures=$((regression_failures + 1))
  fi
}

run_regression check_unregistered_library NonTemplate
run_regression check_unregistered_library Template
run_regression check_original_inductive_casts
run_regression check_relevance
run_regression check_sealed_interfaces SealedInterfaces
run_regression check_sealed_interfaces ImportedSealedInterfaces

if [ "$regression_failures" -ne 0 ]; then
  echo "$regression_failures unsafe-cast regression checks failed"
  exit 1
fi
