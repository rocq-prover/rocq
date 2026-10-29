#!/usr/bin/env bash

# -axiom-free makes the context summary actionable without changing the
# default checker policy. Regression test for #10372.
set -eu

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

compile() {
  local file="$d/$1.v"
  shift
  cat > "$file"
  $coqc -noinit -R "$d" AxiomFree "$@" "$file"
}

compile Safe <<'EOF'
Theorem identity : forall A : Type, forall _ : A, A.
Proof (fun A x => x).

Section Parameters.
  Variable A : Type.
  Variable x : A.
  Definition section_parameter : A := x.
End Parameters.

Module Type Signature.
  Parameter id : forall A : Type, forall _ : A, A.
End Signature.
Module Checked : Signature.
  Definition id (A : Type) (x : A) : A := x.
End Checked.
Module Parameterized (X : Signature).
  Definition id := X.id.
End Parameterized.
EOF

compile ExplicitAxiom <<'EOF'
Axiom assumed : forall A : Type, forall _ : A, A.
EOF
compile TwoAxioms <<'EOF'
Axiom first second : Type.
EOF
compile AdmittedProof <<'EOF'
Theorem unfinished : forall A : Type, forall _ : A, A.
Proof. Admitted.
EOF
compile UnsafeGuard <<'EOF'
Unset Elimination Schemes.
Inductive nat : Set := O | S (n : nat).
#[bypass_check(guard)] Fixpoint loop (n : nat) : nat := loop n.
EOF
compile UnsafeUniverses <<'EOF'
#[bypass_check(universes)] Definition bad := let t := Type in (t : t).
EOF
compile UnsafePositivity <<'EOF'
Unset Elimination Schemes.
#[bypass_check(positivity)]
Inductive bad : Type := roll : forall _ : (forall _ : bad, bad), bad.
EOF
compile Primitives <<'EOF'
Primitive int := #int63_type.
Primitive add := #int63_add.
EOF
compile UnsafeUIP <<'EOF'
Set Definitional UIP.
Definition id (A : Type) (x : A) := x.
EOF
compile SealedUnsafe <<'EOF'
Module Type Signature.
  Parameter value : Type.
End Signature.
Module Sealed : Signature.
  #[bypass_check(universes)] Definition value : Type := Type.
End Sealed.
EOF
compile SealedInductive <<'EOF'
Module Type Empty.
End Empty.
Module Sealed : Empty.
  Unset Elimination Schemes.
  #[bypass_check(positivity)]
  Inductive bad : Type := roll : forall _ : (forall _ : bad, bad), bad.
End Sealed.
EOF
compile SealedAxiom <<'EOF'
Module Type Signature.
  Parameter value : forall A : Type, forall _ : A, A.
End Signature.
Module Sealed : Signature.
  Axiom hidden : forall A : Type, forall _ : A, A.
  Definition value := hidden.
End Sealed.
EOF
compile Rewrite -allow-rewrite-rules <<'EOF'
Definition id (A : Type) (x : A) := x.
EOF
compile Dependency <<'EOF'
From AxiomFree Require Import ExplicitAxiom.
Definition imported := assumed.
EOF

for lib in Safe Primitives SealedUnsafe SealedInductive SealedAxiom; do
  compile "${lib}Dependency" <<EOF
From AxiomFree Require Import $lib.
EOF
done

check() {
  "$BIN"rocqchk -boot -silent -R "$d" AxiomFree "$@"
}

expect_failure() {
  local message="$1"
  shift
  if check "$@" > "$d/out.log" 2>&1 ||
     ! grep -Fq -- "$message" "$d/out.log"; then
    echo "expected rejection: $*"
    cat "$d/out.log"
    exit 1
  fi
}

expect_rejection() {
  check "$@"
  expect_failure 'Axioms or unsafe features found' -axiom-free "$@"
}

# Opaque proofs, section/functor parameters and primitives are safe.
check -axiom-free AxiomFree.Primitives
check -axiom-free -o AxiomFree.Safe > "$d/out.log" 2>&1
grep -q 'Axioms: <none>' "$d/out.log"

# Reject unused/imported axioms, admitted proofs and unsafe flags.
for lib in ExplicitAxiom AdmittedProof UnsafeGuard UnsafeUniverses \
           UnsafePositivity UnsafeUIP SealedUnsafe SealedInductive SealedAxiom Dependency; do
  expect_rejection "AxiomFree.$lib"
done
expect_rejection -o AxiomFree.ExplicitAxiom

# Dependencies loaded without rechecking still contribute their assumptions.
expect_rejection -norec AxiomFree.Dependency
expect_rejection -admit AxiomFree.ExplicitAxiom AxiomFree.Dependency

# Sealed implementations are inspected even when not rechecked.
for lib in SealedUnsafe SealedInductive SealedAxiom; do
  expect_rejection "AxiomFree.${lib}Dependency"
  expect_rejection -norec "AxiomFree.${lib}Dependency"
  expect_rejection -admit "AxiomFree.$lib" "AxiomFree.${lib}Dependency"
done
for lib in Safe Primitives; do
  check -axiom-free "AxiomFree.${lib}Dependency"
  check -axiom-free -norec "AxiomFree.${lib}Dependency"
  check -axiom-free -admit "AxiomFree.$lib" "AxiomFree.${lib}Dependency"
done

# Rewrite permission is unsafe even without symbols or axioms.
expect_rejection AxiomFree.Rewrite

# Impredicative Set is a supported theory, not an unsafe bypass.
check -axiom-free -impredicative-set AxiomFree.Safe

# Allow only the exact names given, and keep them in the report.
rejection='Axioms or unsafe features found'
axiom=AxiomFree.ExplicitAxiom.assumed
check -allow-axiom "$axiom" -axiom-free -o AxiomFree.Dependency > "$d/out.log" 2>&1
grep -Fq "$axiom" "$d/out.log"
check -axiom-free -allow-axiom AxiomFree.Missing.unused AxiomFree.Primitives
for name in assumed AxiomFree.ExplicitAxiom.assume 'AxiomFree.ExplicitAxiom.*'; do
  expect_failure "$rejection" -axiom-free -allow-axiom "$name" AxiomFree.ExplicitAxiom
done
expect_failure "$rejection" -axiom-free -allow-axiom AxiomFree.TwoAxioms.first AxiomFree.TwoAxioms
check -axiom-free -allow-axiom AxiomFree.TwoAxioms.first \
  -allow-axiom AxiomFree.TwoAxioms.second AxiomFree.TwoAxioms

# Allow hidden axioms even when their libraries are not rechecked.
hidden=AxiomFree.SealedAxiom.Sealed.hidden
check -axiom-free -allow-axiom "$hidden" AxiomFree.SealedAxiomDependency
check -axiom-free -allow-axiom "$hidden" -norec AxiomFree.SealedAxiomDependency
check -axiom-free -allow-axiom "$hidden" -admit AxiomFree.SealedAxiom AxiomFree.SealedAxiomDependency

# Naming a declaration cannot permit unsafe features.
for name in UnsafeGuard.loop SealedInductive.Sealed.bad UnsafeUIP.id Rewrite.id; do
  expect_failure "$rejection" -axiom-free -allow-axiom "AxiomFree.$name" "AxiomFree.${name%%.*}"
done
expect_failure '-allow-axiom requires -axiom-free' -allow-axiom "$axiom" AxiomFree.ExplicitAxiom
expect_failure 'Usage:' -axiom-free -allow-axiom
