Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].
Ltac2 check (b : bool) := if b then () else Control.throw Regression_Test_Failure.

Ltac2 count_calls (c1 : constr) (c2 : constr) : int * int :=
  let hits := Ref.ref 0 in
  let misses := Ref.ref 0 in
  Constr.Unsafe.iter2
    (fun _ _ => Ref.set hits (Int.add (Ref.get hits) 1))
    (fun _ _ => Ref.set misses (Int.add (Ref.get misses) 1))
    c1 c2;
  (Ref.get hits, Ref.get misses).

(* same shape: pairs (S, S) and (0, 1) *)
Ltac2 Eval
  let (hits, misses) := count_calls constr:(S 0) constr:(S 1) in
  check (Int.equal hits 2); check (Int.equal misses 0).
(* kind mismatch at the root *)
Ltac2 Eval
  let (hits, misses) := count_calls constr:(S 0) constr:(fun x : nat => x) in
  check (Int.equal hits 0); check (Int.equal misses 1).
(* App alignment: (add 0) 1 vs S 1 gives pairs (add 0, S) and (1, 1) *)
Ltac2 Eval
  let (hits, misses) := count_calls constr:(Nat.add 0 1) constr:(S 1) in
  check (Int.equal hits 2); check (Int.equal misses 0).
(* binders: the accumulator sees the binder of the first term *)
Ltac2 Eval
  let depth_sum := Ref.ref 0 in
  Constr.Unsafe.iter2_with_binders
    (fun n _ => Int.add n 1)
    (fun n _ _ => Ref.set depth_sum (Int.add (Ref.get depth_sum) n))
    (fun _ _ _ => Control.throw Regression_Test_Failure)
    0 constr:(fun x : nat => S x) constr:(fun y : nat => S (S y))
  ;
  check (Int.equal (Ref.get depth_sum) 1). (* nat at 0, bodies at 1 *)
(* leaves with equal kinds produce no calls *)
Ltac2 Eval
  let (hits, misses) := count_calls constr:(true) constr:(false) in
  check (Int.equal hits 0); check (Int.equal misses 0).
