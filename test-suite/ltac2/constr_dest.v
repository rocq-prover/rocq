Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].
Ltac2 check (b : bool) := if b then () else Control.throw Regression_Test_Failure.

Ltac2 Eval
  let (b, body) := Constr.Unsafe.destProd constr:(nat -> bool) in
  check (Constr.equal (Constr.Binder.type b) constr:(nat));
  check (Constr.equal body constr:(bool)).
Ltac2 Eval
  let (b, body) := Constr.Unsafe.destLambda constr:(fun n : nat => n) in
  check (Constr.equal (Constr.Binder.type b) constr:(nat));
  check (Int.equal (Constr.Unsafe.destRel body) 1).
Ltac2 Eval
  let (b, v, body) := Constr.Unsafe.destLetIn constr:(let x := 5 in x) in
  check (Constr.equal (Constr.Binder.type b) constr:(nat));
  check (Constr.equal v constr:(5));
  check (Int.equal (Constr.Unsafe.destRel body) 1).
Ltac2 Eval
  let (f, args) := Constr.Unsafe.destApp constr:(S 0) in
  check (Constr.equal f constr:(S));
  check (Int.equal (Array.length args) 1);
  check (Constr.equal (Array.get args 0) constr:(0)).
Ltac2 Eval
  let (_ind, _inst) := Constr.Unsafe.destInd constr:(nat) in ().
Ltac2 Eval
  let (_cstr, _inst) := Constr.Unsafe.destConstructor constr:(S) in ().
Ltac2 Eval
  let (_cst, _inst) := Constr.Unsafe.destConstant constr:(Nat.add) in ().
Ltac2 Eval
  let _ := Constr.Unsafe.destSort constr:(Prop) in ().
Ltac2 Eval
  let n := Constr.Unsafe.destRel (Constr.Unsafe.make (Constr.Unsafe.Rel 3)) in
  check (Int.equal n 3).
Ltac2 Eval
  let (_ci, _p, _iv, scrut, branches) :=
    Constr.Unsafe.destCase constr:(match 0 with 0 => 1 | S n => n end) in
  check (Constr.equal scrut constr:(0));
  check (Int.equal (Array.length branches) 2).
Ltac2 Eval
  let (_structs, which, tl, bl) := Constr.Unsafe.destFix constr:(fix f (n : nat) : nat := 0) in
  check (Int.equal which 0);
  check (Int.equal (Array.length tl) 1);
  check (Int.equal (Array.length bl) 1).
Fail Ltac2 Eval Constr.Unsafe.destProd constr:(0).
Fail Ltac2 Eval Constr.Unsafe.destApp constr:(S).
Fail Ltac2 Eval Constr.Unsafe.destVar constr:(0).
