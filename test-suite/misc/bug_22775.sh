#!/usr/bin/env bash

set -e

export PATH=$BIN:$PATH
export OCAMLRUNPARAM=s=1

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

N=300

vars() { for i in $(seq 1 $N); do printf ' x%d' "$i"; done; }
zeros() { for i in $(seq 1 $N); do printf ' O'; done; }
sum() {
  for i in $(seq 1 $N); do printf 'Nat.add x%d (' "$i"; done
  printf '%s' "$1"; for i in $(seq 1 $N); do printf ')'; done
}

{
  echo "Definition clos := fun$(vars) : nat => fun y : nat => $(sum y)."
  echo "Definition t1 := Eval vm_compute in clos$(zeros)."
  echo "Definition t2 := Eval vm_compute in clos$(zeros) 0."

  echo "Definition grab := fun$(vars) z : nat => x1."
  echo "Definition t3 := Eval vm_compute in grab$(zeros)."

  echo "Fixpoint grabrec ($(vars) : nat) (n : nat) {struct n} : nat :="
  echo "  match n with O => x1 | S m => grabrec$(vars) m end."
  echo "Definition t4 := Eval vm_compute in grabrec$(zeros)."
  echo "Definition t5 := Eval vm_compute in fun n => grabrec$(zeros) n."
  echo "Definition t6 := Eval vm_compute in grabrec$(zeros) 5."

  echo "Definition fx := fun$(vars) : nat =>"
  echo "  fix f1 (n : nat) : nat := match n with O => $(sum O) | S m => f2 m end"
  echo "  with f2 (n : nat) : nat := match n with O => O | S m => f1 m end for f1."
  echo "Definition t7 := Eval vm_compute in fx$(zeros) 1000."
  echo "Definition t8 := Eval vm_compute in fun n => fx$(zeros) (S n)."
} > "$d/bug_22775.v"

${coqc#"$BIN"} "$d/bug_22775.v"
