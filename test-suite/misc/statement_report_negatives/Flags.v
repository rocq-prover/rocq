(* Relaxed typing conditions for misc/statement_report_negatives.sh: each
   model reaches exactly one object declared under one of them, the last one
   only through the implementation of a sealed module. *)

#[bypass_check(guard)] Fixpoint g (n : nat) : nat := g n.

#[bypass_check(universes)] Definition tt_T := let t := Type in (t : t).

#[bypass_check(positivity)] Inductive Bad : Type := C : (Bad -> nat) -> Bad.
Definition uses_bad (b : Bad) : nat := O.

Module UIP.
  Set Definitional UIP.
  Inductive seq {A} (a : A) : A -> SProp := srefl : seq a a.
End UIP.
Definition useq := UIP.srefl O.

Module Type NSIG.
  Parameter thm : nat.
End NSIG.
Module HG : NSIG.
  #[bypass_check(guard)] Fixpoint loop (n : nat) : nat := loop n.
  Definition thm := loop O.
End HG.
Definition uses_hidden : nat := HG.thm.


(* An opaque body that the signature hides: its axiom is read from the
   library's table of opaque proofs. *)
Axiom oax : nat.
Module Opq : NSIG.
  Lemma thm : nat.
  Proof. exact oax. Qed.
End Opq.
Definition opaque_hidden : nat := Opq.thm.