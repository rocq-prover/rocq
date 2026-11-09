#!/usr/bin/env bash
# VM structured constants must keep the same sharing across garbage collections.
set -eu
export PATH="$BIN:$PATH"

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

python3 - "$d/Repro.v" <<'PY'
import pathlib
import sys

tree = '(leaf (S (S O)))'
for _ in range(12):
    tree = '(node ' + tree + ' ' + tree + ')'
pathlib.Path(sys.argv[1]).write_text('''Unset Elimination Schemes.
Inductive nat : Set := O | S : forall (_ : nat), nat.
Inductive tree : Set := leaf : forall (_ : nat), tree | node : forall (_ _ : tree), tree.
Definition repro := ''' + tree + '.\n')
PY

OCAMLRUNPARAM=s=4k rocq compile -q -noinit -native-compiler no "$d/Repro.v"
cp "$d/Repro.vo" "$d/small.vo"
OCAMLRUNPARAM=s=64M rocq compile -q -noinit -native-compiler no "$d/Repro.v"
cmp "$d/small.vo" "$d/Repro.vo"
