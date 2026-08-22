(* Source-only counterexample to nested-fixpoint uniformity analysis. *)
Definition relay (outer : nat -> Type) (seed : nat) : nat -> nat -> Type :=
  fix inner (carry : nat := seed) (p m : nat) {struct m} : Type :=
    match m with
    | O => outer p -> False
    | S rest => inner carry rest
    end.

Fail
Fixpoint russell (n : nat) : Type :=
  match n with
  | O => True
  | S smaller => relay russell n smaller smaller
  end.

(*
Definition diagonal (x : russell 2) : False := x x.
Definition contradiction : False := diagonal diagonal.

Print Assumptions contradiction.
*)

#[refine]
Fixpoint error (n : nat) : nat :=
  match n with 0 => 0 | S n' => _ n' 1 end.
Proof.
  fix rec 2.
  exact ((fun (p : nat) (q r : nat) => match r with 0 => 1 + error q | S r' => rec p r' end) 1).
  Fail Guarded.
Abort.
