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

(* The signature declares [p] without guard checking, at a type that reaches
   the unchecked fixpoint [g]; the implementations declare it with guard
   checking, at [nat]. [FD] is in the environment; [OF.I] is hidden inside a
   sealed module, with its signature. *)
Definition ft : Type := (fun (_ : nat) (A : Type) => A) (g O) nat.
Module Type FSIG.
  Unset Guard Checking.
  Parameter p : ft.
  Set Guard Checking.
End FSIG.
Module FD : FSIG.
  Definition p : nat := O.
End FD.
Definition uses_fd : nat := FD.p.
Module OF : NSIG.
  Module I : FSIG.
    Definition p : nat := O.
  End I.
  Definition thm : nat := I.p.
End OF.
Definition uses_of : nat := OF.thm.

(* An interface that gives [p] its own opaque proof, which an implementation
   with another body satisfies: the environment holds the interface's proof,
   and the closure must also follow the implementation's. *)
Axiom iax : nat.
Module Type PSIG.
  Lemma p : nat.
  Proof. exact O. Qed.
End PSIG.
Module PB : PSIG.
  Definition p : nat := iax.
End PB.
Definition uses_pb : nat := PB.p.

(* An inductive whose interface gives a constructor another type, convertible
   to its implementation's, and its own typing flags; the module is hidden
   inside a sealed module. *)
Axiom tax : nat.
Definition TT : Set := (fun _ : nat => nat) tax.
Module Type ISIG.
  Unset Positivity Checking.
  Inductive t : Set := c : TT -> t.
  Set Positivity Checking.
End ISIG.
Module OI : NSIG.
  Module I : ISIG.
    Inductive t : Set := c : nat -> t.
  End I.
  Definition thm : nat := match I.c O with I.c _ => O end.
End OI.
Definition uses_oi : nat := OI.thm.

(* An opaque body that the signature hides: its axiom is read from the
   library's table of opaque proofs. *)
Axiom oax : nat.
Module Opq : NSIG.
  Lemma thm : nat.
  Proof. exact oax. Qed.
End Opq.
Definition opaque_hidden : nat := Opq.thm.
