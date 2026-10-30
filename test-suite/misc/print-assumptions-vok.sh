#!/bin/sh
set -e

# Use rocq c instead of $coqc to work in async mode
export PATH="$BIN:$PATH"

rocq c -q -R misc/print-assumptions-vok/ PrintAssumptionsVOK -vos misc/print-assumptions-vok/file1.v
rocq c -q -R misc/print-assumptions-vok/ PrintAssumptionsVOK -vos misc/print-assumptions-vok/file2.v
log=$(mktemp)
trap 'rm -f "$log"' EXIT
if ! rocq c -q -R misc/print-assumptions-vok/ PrintAssumptionsVOK -vok misc/print-assumptions-vok/file2.v > "$log" 2>&1; then
  cat "$log"
  exit 1
fi
cat "$log"
grep -Fq 'Sealed.value : True' "$log"
if grep -Eq '^Axioms:|^Closed under the global context' "$log"; then
  echo "An inaccessible signature proof was treated as an axiom or as assumption-free"
  exit 1
fi
