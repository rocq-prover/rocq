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
