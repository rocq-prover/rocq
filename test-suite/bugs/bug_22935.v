From Corelib Require Import PrimInt63 PrimArray PrimFloat.

Open Scope array_scope.

(* Constant array literals of length >= 2 were compiled to statically allocated
   OCaml tuples and mutated in place by PrimArray.set during native evaluation. *)
Fixpoint run_bool (n : nat) (prev : array bool) : bool :=
  let cur := [| true; true | true |] in
  match n with
  | 0 => cur.[0]
  | S k =>
    let mutated := cur.[0 <- false] in
    match mutated.[0] with
    | true => true
    | false => run_bool k mutated
    end
  end.

Fail Definition bad_bool : run_bool 1 [| | true |] = false :=
  eq_refl false <<: run_bool 1 [| | true |] = false.

Definition good_bool : run_bool 1 [| | true |] = true :=
  eq_refl true <<: run_bool 1 [| | true |] = true.

(* Float array literals must remain non-flat (tag 0) after copying and updating. *)
Fixpoint run_float (n : nat) (prev : array float) : float :=
  let cur := [| 1%float; 2%float | 0%float |] in
  match n with
  | 0 => cur.[0]
  | S k =>
    let mutated := cur.[0 <- 2%float] in
    match PrimFloat.Leibniz.eqb mutated.[0] 2%float with
    | false => 0%float
    | true => run_float k mutated
    end
  end.

Definition good_float : PrimFloat.Leibniz.eqb (run_float 1 [| | 0%float |]) 1%float = true :=
  eq_refl true <<: PrimFloat.Leibniz.eqb (run_float 1 [| | 0%float |]) 1%float = true.
