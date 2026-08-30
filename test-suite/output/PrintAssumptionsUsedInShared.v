(** The same empty [match] written twice is ONE subterm once the proof has
    been hash-consed, so it is reached once and reported once.  The walk used
    to reach it once per path through the term, and to report the identical
    elimination once per path. *)

Axiom bad : False.

Lemma twice : nat * nat.
Proof.
  exact (pair (match bad return nat with end) (match bad return nat with end)).
Qed.

Print Assumptions twice.
