Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].
Ltac2 check (b : bool) := if b then () else Control.throw Regression_Test_Failure.

(* [(S : nat -> nat)] keeps its cast node; build [((S : nat -> nat) 0)]
   by hand so the cast sits between two applications. *)
Ltac2 cast_s () : constr := constr:((S : nat -> nat)).
Ltac2 casted_app () : constr :=
  Constr.Unsafe.make (Constr.Unsafe.App (cast_s ()) [| constr:(0) |]).

Ltac2 Eval check (Constr.equal (Constr.strip_cast (cast_s ())) constr:(S)).
Ltac2 Eval check (Constr.equal (Constr.strip_cast constr:(0)) constr:(0)).
Ltac2 Eval check (Constr.equal (Constr.head constr:(Nat.add 1 2)) constr:(Nat.add)).
Ltac2 Eval check (Constr.equal (Constr.head constr:(S)) constr:(S)).
Ltac2 Eval check (Constr.equal (Constr.head (casted_app ())) (cast_s ())).
Ltac2 Eval check (Constr.equal (Constr.head_nocast (casted_app ())) constr:(S)).
Ltac2 Eval
  let (f, args) := Constr.decompose_app_nocast (casted_app ()) in
  check (Constr.equal f constr:(S));
  check (Int.equal (Array.length args) 1);
  check (Constr.equal (Array.get args 0) constr:(0)).
Ltac2 Eval
  let (f, args) := Constr.decompose_app_nocast constr:(Nat.add 1 2) in
  check (Constr.equal f constr:(Nat.add));
  check (Int.equal (Array.length args) 2).
Ltac2 Eval
  let (f, args) := Constr.decompose_app_list_nocast constr:(Nat.add 1 2) in
  check (Constr.equal f constr:(Nat.add));
  check (List.equal Constr.equal args [constr:(1); constr:(2)]).
Ltac2 Eval
  let (f, args) := Constr.decompose_app_nocast constr:(0) in
  check (Constr.equal f constr:(0));
  check (Int.equal (Array.length args) 0).
