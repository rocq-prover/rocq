Declare ML Module "unsafe_cast.plugin".

(* Registration alone must not taint ordinary definitions. *)
Definition ordinary := 0.
Print Assumptions ordinary.

Definition lhs : 2 + 2 = 4 := eq_refl.
Definition rhs := 2 + 2 = 4.

(* Normalize only lhs's inferred type, then resume ordinary conversion with
   the unchanged, reducible rhs constant. *)
Definition vm_source := lhs <:["test.vm-lhs"] rhs.
Print vm_source.
Print Assumptions vm_source.
Definition transitive := vm_source.
Print Assumptions transitive.

Fail Check (lhs <:["test.missing"] rhs).
Fail Check (lhs <:["test.reject"] rhs).
Fail Check (lhs <:["test.vm-lhs"] (2 = 3)).
Fail Check ((true : nat) <:["test.accept"] nat).
Fail Check (0 <:["test.accept"] 0).

(* Local variables are supported when their types contain no evars. *)
Definition local (n : nat) (p : n + 0 = n) :=
  p <:["test.vm-lhs"] (n + 0 = n).
Print Assumptions local.

(* A target preparation hook can infer an evar in the source, as in PR #20503. *)
Inductive value_of {A : Type} : A -> Type := value_is a : value_of a.
Definition inferred := @value_is nat _ <:["test.vm-rhs"] @value_of nat (2 + 2).
Check inferred : value_of 4.
Print Assumptions inferred.

(* Reject evars in callback-visible inputs, including the environment. *)
Fail Check (fun (x : _) => lhs <:["test.vm-lhs"] rhs).
Fail Check (@value_is nat _ <:["test.vm-lhs"] @value_of nat (2 + 2)).

Lemma opaque_direct : rhs.
Proof. exact (lhs <:["test.vm-lhs"] rhs). Qed.
Print Assumptions opaque_direct.

Definition type_only : (nat <:["test.vm-lhs"] Set) := 0.
Print Assumptions type_only.
Axiom type_axiom : (nat <:["test.vm-lhs"] Set).
Print Assumptions type_axiom.

Inductive arity_cast : (Prop <:["test.vm-lhs"] Type) := arity_constructor.
Print Assumptions arity_cast.
Inductive constructor_cast : Set :=
  cast_constructor : (constructor_cast <:["test.vm-lhs"] Set).
Print Assumptions cast_constructor.

Section ContextCast.
  Variable x : (nat <:["test.vm-lhs"] Set).
  Definition section_use := x.
  Print Assumptions section_use.
End ContextCast.
Print Assumptions section_use.

Module Type Signature. Parameter proof : rhs. End Signature.
Module Sealed : Signature.
  Definition proof := lhs <:["test.vm-lhs"] rhs.
End Sealed.
Print Assumptions Sealed.proof.

(* This is intentionally inconsistent, and must never look assumption-free. *)
Definition unsafe_false : False := 0 <:["test.accept"] False.
Print Assumptions unsafe_false.
Definition nested := (0 <:["test.accept"] nat) <:["test.vm-lhs"] nat.
Print Assumptions nested.

(* Merely erasing a cast for evaluation does not mutate the stored proof. *)
Eval cbv in nested.
Print Assumptions nested.

(* Cast checking uses cumulativity, not equality of universes. *)
Universe u v.
Constraint u < v.
Definition cumulative (A : Type@{u}) := A <:["test.vm-lhs"] Type@{v}.
Print Assumptions cumulative.

(* Ltac2 can construct the same named cast kind without going through syntax. *)
From Ltac2 Require Import Ltac2.
Goal rhs.
Proof.
  let k := Constr.Cast.unsafe "test.vm-lhs" in
  let c := Constr.Unsafe.make (Constr.Unsafe.Cast constr:(lhs) k constr:(rhs)) in
  Control.refine (fun () => c).
Qed.

(* Build the predicate directly: ordinary match elaboration normalizes it.
   Print Assumptions' empty-elimination shortcut must still inspect this cast. *)
Axiom absurd : False.
Definition eliminated : nat.
Proof.
  let c := constr:(match absurd return nat with end) in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Case ci (p, rel) inv scrut branches =>
    match Constr.Unsafe.kind p with
    | Constr.Unsafe.Lambda binder ret =>
      let k := Constr.Cast.unsafe "test.vm-lhs" in
      let ret := Constr.Unsafe.make (Constr.Unsafe.Cast ret k constr:(Set)) in
      let p := Constr.Unsafe.make (Constr.Unsafe.Lambda binder ret) in
      let c := Constr.Unsafe.make (Constr.Unsafe.Case ci (p, rel) inv scrut branches) in
      Std.exact_no_check c
    | _ => Control.throw Assertion_failure
    end
  | _ => Control.throw Assertion_failure
  end.
Defined.
Print Assumptions eliminated.
