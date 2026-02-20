Require Import Ltac2.Ltac2.

Ltac2 Declare Scope sc1.
Ltac2 Declare Scope sc2.

Ltac2 Notation "foo" x(constr) % sc1 := x.
Ltac2 Notation "foo" y(open_constr) % sc2 := y.

Ltac2 Notation "foo'" % sc1 := 0.
Ltac2 Notation "foo'" % sc2 := 1.

Fail Ltac2 testbad () := foo tt.
Fail Ltac2 testbad' () := foo'.
(* scopes not open *)

Ltac2 Open Scope sc1.
Ltac2 test1 () := foo _.
Ltac2 test1' := foo'.

Ltac2 Open Scope sc2.
Ltac2 test2 () := foo _.
Ltac2 test2' := foo'.

Fail Ltac2 Eval test1().
(* _ interpreted as constr *)

Ltac2 Eval Control.assert_true (Int.equal test1' 0).

Ltac2 Eval test2().

Ltac2 Eval Control.assert_true (Int.equal test2' 1).

Ltac2 Notation "bar" := foo _.

Ltac2 Abbreviation bar' := foo'.

Ltac2 Close Scope sc2.

Fail Ltac2 Eval test1().
Ltac2 Eval test2().
Ltac2 Eval bar.

(* interp of foo' in bar' was decided at time of declaration of bar', when sc2 was open *)
Ltac2 Eval Control.assert_true (Int.equal bar' 1).

(* another scope closing test *)
Ltac2 Close Scope sc1.
Fail Ltac2 Eval foo tt.

(* we can also close the default scope *)
Ltac2 Close Scope core.
Fail Ltac2 Eval intros _.
Ltac2 Open Scope core.

(* constr delimiters are also controlled by scopes *)
Ltac2 Notation "myconstr" x(constr(type)) % sc1 := x.
Ltac2 Notation "myconstr" x(constr(nat)) % sc2 := x.

Ltac2 Open Scope sc1.

Ltac2 Eval myconstr (nat * nat).
Fail Ltac2 Eval myconstr (0 * 0).

Ltac2 Open Scope sc2.

Fail Ltac2 Eval myconstr (nat * nat).
Ltac2 Eval myconstr (0 * 0).

(* notations with identical parsing in different custom entries don't interfere *)
Ltac2 Custom Entry custom.

Ltac2 Notation "custest" x(tactic(0)) := (Int.equal x 1).

Ltac2 Eval Control.assert_true (custest 1).

Ltac2 Notation "custest" x(tactic(0)) : custom(0) := (Int.equal x 2).

Ltac2 Eval Control.assert_true (custest 1).
