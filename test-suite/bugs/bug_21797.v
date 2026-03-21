(* The function Inductive.find_uniform_parameters did not recurse
   into arguments of Rel applications.
   A self-call hidden inside a regular function application was invisible
   to the uniform parameter analysis, causing over-counting. *)
Fail Fixpoint naughty (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    (fix G (a : nat) (f : nat -> nat -> nat) (m : nat) {struct m} : nat :=
      match m with
      | 0 => S (naughty a)
      | S m' => f (G n f m') m'
      end) n' (fun x _ => x) n'
  end.

(*
Lemma naughty_loop : naughty 2 = S (naughty 2).
Proof.
remember 0 as n.
set (v := naughty (S (S n))) at 2.
remember v as ans; unfold v in *; clearbody v.
cbn.
set (n₀ := n) at 3.
replace n₀ with 0.
f_equal.
now symmetry.
Qed.

Theorem inconsistency : False.
Proof.
  assert (Hn : forall n, n <> S n).
  { induction n; discriminate + (intro H; apply IHn; now injection H). }
  exact (Hn _ naughty_loop).
Qed.

Print Assumptions inconsistency.
*)

(** Another variant of the same issue *)

Fixpoint iter_fg {A} f g (a : A) n :=
  match n with
  | 0 => a | S n' => f (iter_fg f g (g a) n')
  end.

Fail Fixpoint F (n : nat) :=
  iter_fg S F n 1.

(*
Theorem wrong : F 0 = S (F 0).
Proof.
  unfold F at 1. change (fix F (n : nat) := _) with F.
  cbn -[F]. reflexivity.
Qed.

Corollary false : False.
Proof.
  assert (H : forall n, n <> S n).
  { induction n; eauto. }
  eapply H, wrong.
Qed.
*)
