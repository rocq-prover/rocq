Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].
Ltac2 check (b : bool) := if b then () else Control.throw Regression_Test_Failure.

Ltac2 Eval check (Constr.equal (Constr.Unsafe.mkApp constr:(S) [| constr:(0) |]) constr:(S 0)).
Ltac2 Eval check (Constr.equal (Constr.Unsafe.mkApp_list constr:(Nat.add) [constr:(1); constr:(2)]) constr:(Nat.add 1 2)).
Ltac2 Eval
  (* rebuild constrs from their own kinds via the wrappers *)
  match Constr.Unsafe.kind constr:(nat -> bool) with
  | Constr.Unsafe.Prod b body => check (Constr.equal (Constr.Unsafe.mkProd b body) constr:(nat -> bool))
  | _ => Control.throw Regression_Test_Failure
  end.
Ltac2 Eval
  match Constr.Unsafe.kind constr:(fun n : nat => n) with
  | Constr.Unsafe.Lambda b body => check (Constr.equal (Constr.Unsafe.mkLambda b body) constr:(fun n : nat => n))
  | _ => Control.throw Regression_Test_Failure
  end.
Ltac2 Eval
  match Constr.Unsafe.kind constr:(let x := 5 in x) with
  | Constr.Unsafe.LetIn b v body => check (Constr.equal (Constr.Unsafe.mkLetIn b v body) constr:(let x := 5 in x))
  | _ => Control.throw Regression_Test_Failure
  end.
Ltac2 Eval
  match Constr.Unsafe.kind constr:(nat) with
  | Constr.Unsafe.Ind ind inst => check (Constr.equal (Constr.Unsafe.mkInd ind inst) constr:(nat))
  | _ => Control.throw Regression_Test_Failure
  end.
Ltac2 Eval
  match Constr.Unsafe.kind constr:(S) with
  | Constr.Unsafe.Constructor cstr inst => check (Constr.equal (Constr.Unsafe.mkConstructor cstr inst) constr:(S))
  | _ => Control.throw Regression_Test_Failure
  end.
Ltac2 Eval
  match Constr.Unsafe.kind constr:(Nat.add) with
  | Constr.Unsafe.Constant cst inst => check (Constr.equal (Constr.Unsafe.mkConstant cst inst) constr:(Nat.add))
  | _ => Control.throw Regression_Test_Failure
  end.
Ltac2 Eval
  match Constr.Unsafe.kind constr:(match 0 with 0 => 1 | S n => n end) with
  | Constr.Unsafe.Case ci p iv scrut branches =>
      check (Constr.equal (Constr.Unsafe.mkCase ci p iv scrut branches)
                          constr:(match 0 with 0 => 1 | S n => n end))
  | _ => Control.throw Regression_Test_Failure
  end.
Ltac2 Eval
  match Constr.Unsafe.kind constr:(Prop) with
  | Constr.Unsafe.Sort s => check (Constr.equal (Constr.Unsafe.mkSort s) constr:(Prop))
  | _ => Control.throw Regression_Test_Failure
  end.
Ltac2 Eval check (match Constr.Unsafe.kind (Constr.Unsafe.mkRel 1) with
                  | Constr.Unsafe.Rel n => Int.equal n 1
                  | _ => false
                  end).
Ltac2 Eval check (Constr.equal
  (Constr.Unsafe.mkArrow (Some Constr.Binder.Relevant) constr:(nat) constr:(bool))
  constr:(nat -> bool)).
