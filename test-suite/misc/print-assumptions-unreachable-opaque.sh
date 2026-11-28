#!/usr/bin/env bash

# Print Assumptions warns, and does not fail, when the .vo file of an opaque
# proof is removed after the library is loaded.
set -eu

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

echo 'Lemma foo : True. Proof. exact I. Qed.' > "$d/A.v"
$coqc -R "$d" Test "$d/A.v"

mkfifo "$d/in" "$d/out"
"$BIN"rocq repl -q -R "$d" Test < "$d/in" > "$d/out" 2>&1 &
exec 3> "$d/in" 4< "$d/out"
echo 'From Test Require A. Check A.foo.' >&3
# the output of Check tells that A is loaded, so A.vo can go
line=
: > "$d/log"
while read -r -t 60 line <&4; do
  printf '%s\n' "$line" >> "$d/log"
  [ "$line" = ': True' ] && break
done
[ "$line" = ': True' ] || { printf '%s\n' "$line" >> "$d/log"; cat "$d/log"; exit 1; }
rm "$d/A.vo"
echo 'Print Assumptions A.foo.' >&3
exec 3>&-
cat <&4 >> "$d/log"
cat "$d/log"

if ! grep -q -F '[unreachable-opaque-body,' "$d/log" ||
   ! grep -q -F 'Opaque proofs that could not be accessed:' "$d/log" ||
   grep -q -F 'Error:' "$d/log"
then exit 1; fi
