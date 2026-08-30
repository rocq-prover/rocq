(** [Print Assumptions] reports, for an axiom that a proof eliminates with an
    empty [match], WHERE the elimination happens: that is the [ax2ty] map of
    [Assumptions], and it is the only part of the command's answer that
    depends on how many times the traversal reaches a given subterm.  A
    traversal that skips subterms it has already walked must still report an
    elimination in every constant it occurs in, and every distinct
    elimination inside one constant. *)

Axiom bad : False.

(** Two eliminations that differ: both are reported. *)

Lemma two_types : nat * bool.
Proof.
  exact (pair (match bad return nat with end) (match bad return bool with end)).
Qed.

Print Assumptions two_types.

(** The same elimination in two different constants: reported once for each,
    even though the two proofs share the subterm. *)

Lemma first : nat.
Proof. exact (match bad return nat with end). Qed.

Lemma second : nat.
Proof. exact (match bad return nat with end). Qed.

Definition both := pair first second.

Print Assumptions both.

(** An axiom that is not eliminated this way carries no such report, ... *)

Axiom foo : nat.

Lemma plain : nat * nat.
Proof. exact (pair foo foo). Qed.

Print Assumptions plain.

(** ... and neither does [destruct], which goes through [False_ind]. *)

Lemma by_destruct : nat.
Proof. destruct bad. Qed.

Print Assumptions by_destruct.
