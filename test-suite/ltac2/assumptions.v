Require Import Ltac2.Ltac2.
Require Import Ltac2.Env.
Require Import Ltac2.TransparentState.

(* Test axiom *)
Axiom test_axiom : nat.

(* Test opaque definition *)
Definition test_opaque : nat. Proof. exact 0. Qed.

(* Test transparent definition *)
Definition test_transparent : nat := 0.

(* Test definition that depends on an axiom *)
Definition depends_on_axiom : nat := test_axiom.

(* Basic test: assumptions on an axiom returns itself *)
Ltac2 Eval
  let asms := Env.assumptions false false TransparentState.full [reference:(test_axiom)] in
  Control.assert_true (Int.equal (List.length asms) 1).

(* Test: assumptions on transparent definition with no axioms returns empty *)
Ltac2 Eval
  let asms := Env.assumptions false false TransparentState.full [reference:(test_transparent)] in
  Control.assert_true (Int.equal (List.length asms) 0).

(* Test: assumptions on definition depending on axiom finds the axiom *)
Ltac2 Eval
  let asms := Env.assumptions false false TransparentState.full [reference:(depends_on_axiom)] in
  Control.assert_true (Int.equal (List.length asms) 1).

(* Test: is_axiom accessor *)
Ltac2 Eval
  let asms := Env.assumptions false false TransparentState.full [reference:(test_axiom)] in
  match asms with
  | (a, _) :: _ => Control.assert_true (Env.Assumption.is_axiom a)
  | [] => Control.throw Assertion_failure
  end.

(* Test: is_opaque accessor with add_opaque=true *)
Ltac2 Eval
  let asms := Env.assumptions true false TransparentState.full [reference:(test_opaque)] in
  Control.assert_true (Int.equal (List.length asms) 1).

Ltac2 Eval
  let asms := Env.assumptions true false TransparentState.full [reference:(test_opaque)] in
  match asms with
  | (a, _) :: _ => Control.assert_true (Env.Assumption.is_opaque a)
  | [] => Control.throw Assertion_failure
  end.

(* Test: is_transparent accessor with add_transparent=true *)
Ltac2 Eval
  let asms := Env.assumptions false true TransparentState.full [reference:(test_transparent)] in
  Control.assert_true (Int.equal (List.length asms) 1).

Ltac2 Eval
  let asms := Env.assumptions false true TransparentState.full [reference:(test_transparent)] in
  match asms with
  | (a, _) :: _ => Control.assert_true (Env.Assumption.is_transparent a)
  | [] => Control.throw Assertion_failure
  end.

(* Test: reference accessor *)
Ltac2 Eval
  let asms := Env.assumptions false false TransparentState.full [reference:(test_axiom)] in
  match asms with
  | (a, _) :: _ =>
    match Env.Assumption.reference a with
    | Std.ConstRef _ => ()
    | _ => Control.throw Assertion_failure
    end
  | [] => Control.throw Assertion_failure
  end.

(* Test: other accessors return false for plain axiom *)
Ltac2 Eval
  let asms := Env.assumptions false false TransparentState.full [reference:(test_axiom)] in
  match asms with
  | (a, _) :: _ =>
    Control.assert_false (Env.Assumption.is_opaque a);
    Control.assert_false (Env.Assumption.is_transparent a);
    Control.assert_false (Env.Assumption.assumes_positive a);
    Control.assert_false (Env.Assumption.assumes_guarded a);
    Control.assert_false (Env.Assumption.assumes_type_in_type a);
    Control.assert_false (Env.Assumption.assumes_uip a)
  | [] => Control.throw Assertion_failure
  end.
