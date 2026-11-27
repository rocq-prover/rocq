#!/usr/bin/env bash

# A mutual cofixpoint of 300 functions has a closure of more than
# Max_young_wosize words, so the copy of it that vm_compute's read-back makes
# (mk_cofix_body in kernel/vmvalues.ml) is in the major heap. The read-back
# writes a code pointer in field 0 of that copy. With OCAMLRUNPARAM=o=1 the
# major GC marks most of the time, so many of those writes happen while it
# marks; a write through the OCaml write barrier then hands the GC the old
# code pointer as if it were a heap block. The read-back is done 200 times.

set -e

export PATH=$BIN:$PATH
export OCAMLRUNPARAM=o=1

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

N=300
R=200

{
  echo "CoInductive stream := Cons : nat -> stream -> stream."
  printf 'Definition c := cofix c1 : stream := Cons O c2\n'
  for i in $(seq 2 $N); do
    j=$(( i % N + 1 ))
    printf 'with c%d : stream := Cons O c%d\n' "$i" "$j"
  done
  printf 'for c1.\n'
  for k in $(seq 1 $R); do
    echo "Definition t$k := Eval vm_compute in c."
  done
} > "$d/bug_cofix_barrier.v"

# A crash fails the test; a CPU-time limit turns a loop into a failure too.
(ulimit -t 900; ${coqc#"$BIN"} -native-compiler no "$d/bug_cofix_barrier.v")
