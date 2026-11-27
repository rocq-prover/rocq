#!/bin/sh
# Test rocq c compiled with wasm_of_ocaml (rocq-web), under node.
#
# Usage: run.sh ROCQ_C COQLIB
#   ROCQ_C  rocq_c.bc.wasm.js, as installed by rocq-web
#   COQLIB  the Rocq library (rocq c -where) of the native Rocq the
#           libraries of rocq-web come from
#
# 1. Every module of Corelib is required: the .vo files are produced by a
#    64 bits Rocq, and under wasm_of_ocaml OCaml integers have 31 bits,
#    hence input_value fails ("integer too large") on a .vo containing an
#    integer which does not fit 31 bits. The modules known to contain one
#    are listed in KNOWN_FAILURES: they must still fail, so that the list
#    is kept up to date.
# 2. uint63.v computes with primitive integers which do not fit 31 bits.
#    It also parses and prints numbers (number notations), which needs
#    rocq c not to make bytecode for the VM (the default under wasm).
set -u

if [ $# -ne 2 ]; then echo "usage: $0 ROCQ_C COQLIB" >&2; exit 2; fi
rocq_c=$1
coqlib=$2
here=$(cd "$(dirname "$0")" && pwd)

# Sint63Axioms: Definition min_int := Eval lazy in (lsl 1 62).
KNOWN_FAILURES="Corelib.Numbers.Cyclic.Int63.Sint63Axioms"

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

rocq_c () { (cd "$tmp" && node "$rocq_c" -coqlib "$coqlib" "$@"); }

is_known () {
  for k in $KNOWN_FAILURES; do [ "$k" = "$1" ] && return 0; done
  return 1
}

fail=0

# The modules of Corelib, from the installed .vo files
modules=$(cd "$coqlib/theories" && find . -name '*.vo' |
  sed -e 's|^\./||' -e 's|\.vo$||' -e 's|/|.|g' -e 's|^|Corelib.|' | sort)
if [ -z "$modules" ]; then echo "FAIL no .vo in $coqlib/theories"; exit 1; fi

: > "$tmp/corelib.v"
for m in $modules; do
  is_known "$m" || echo "Require $m." >> "$tmp/corelib.v"
done
if rocq_c corelib.v > "$tmp/corelib.out" 2>&1; then
  echo "OK   Corelib ($(echo "$modules" | wc -l) modules, known failures excluded)"
else
  echo "FAIL Corelib:"; sed 's/^/  /' "$tmp/corelib.out"
  # rocq c stops at the first error: find all the modules failing
  for m in $modules; do
    is_known "$m" && continue
    echo "Require $m." > "$tmp/one.v"
    rocq_c one.v > "$tmp/one.out" 2>&1 ||
      { echo "FAIL $m"; sed 's/^/  /' "$tmp/one.out"; }
  done
  fail=1
fi

for m in $KNOWN_FAILURES; do
  echo "Require $m." > "$tmp/one.v"
  if rocq_c one.v > "$tmp/one.out" 2>&1; then
    echo "FAIL $m loads: remove it from KNOWN_FAILURES in $0"; fail=1
  elif grep -q "integer too large" "$tmp/one.out"; then
    echo "OK   $m fails as expected (integer too large)"
  else
    echo "FAIL $m fails, not with \"integer too large\":"
    sed 's/^/  /' "$tmp/one.out"; fail=1
  fi
done

cp "$here/uint63.v" "$tmp/"
if rocq_c uint63.v > "$tmp/uint63.out" 2>&1; then
  echo "OK   uint63.v"
else
  echo "FAIL uint63.v:"; sed 's/^/  /' "$tmp/uint63.out"; fail=1
fi

exit $fail
