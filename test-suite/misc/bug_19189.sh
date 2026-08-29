#!/bin/sh
# Batch compilation with -async-proofs on must report the original error
# instead of absorbing it (#19189).
set -e

TMP=misc/bug_19189.tmp
rm -rf $TMP
mkdir -p $TMP
cp misc/bug_19189/*.v $TMP/

# A failing tactic before Abort must surface.
if $coqc -async-proofs on $TMP/abort_section.v > $TMP/abort.log 2>&1; then
  echo "abort_section.v should have failed"; cat $TMP/abort.log; exit 1
fi
if ! grep -q "Tactic failure" $TMP/abort.log; then
  echo "expected the real error (Tactic failure), got:"; cat $TMP/abort.log; exit 1
fi
if grep -q "Open proofs remain" $TMP/abort.log; then
  echo "bogus error reported at End:"; cat $TMP/abort.log; exit 1
fi

# An ill-typed definition before a delegated proof must fail.
if $coqc -async-proofs on $TMP/baddef_section.v > $TMP/baddef.log 2>&1; then
  echo "baddef_section.v should have failed"; cat $TMP/baddef.log; exit 1
fi
if ! grep -q "expected to have type" $TMP/baddef.log; then
  echo "expected the real error (type error on d), got:"; cat $TMP/baddef.log; exit 1
fi

# Valid control.
$coqc -async-proofs on $TMP/valid_section.v > $TMP/valid.log 2>&1

rm -rf $TMP
