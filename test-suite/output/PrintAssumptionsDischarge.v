(** [Print Assumptions] walks an opaque proof as stored, before the section
    discharge, and has to answer as if it walked the discharged proof.  Where
    the two differ is the "used in" report of an empty [match] on an axiom:
    what the goal looks like once discharged, and whether the matched
    constant is still an axiom on its own or one applied to section
    variables. *)

Axiom bad : False.
Axiom gA : nat.
Inductive E (n : nat) : Prop := .

Section S.
  Variable u : nat.
  Definition k := u + 1.

  (** The goal mentions a constant the discharge applies to [u]. *)
  Lemma usedin_arg : k = k.
  Proof. exact (match bad return k = k with end). Qed.

  (** Several binders below the root, some of which mention [u] or [k]:
      the goal is cooked at its own depth. *)
  Lemma usedin_deep : forall n : nat, n = k -> k = n.
  Proof.
    exact (fun n (e : n = k) =>
      let m := k + n in
      match m with
      | O => match bad return k = n with end
      | S p => let q := match bad return k + p = k + m with end in
               match bad return k = n with end
      end).
  Qed.

  (** [ax2] is discharged to [ax2 u], so this is no longer a match on an
      axiom: [ax2] and the axiom its type depends on are reported. *)
  Lemma ax2 : E gA.
  Proof using u. Admitted.
  Lemma usedin_applied : 0 = 0.
  Proof. exact (match ax2 return 0 = 0 with end). Qed.

  (** A section [Let] is a local definition of the discharged proof. *)
  Let la := u + 2.
  Lemma usedin_let : la = la.
  Proof. exact (match bad return la = la with end). Qed.
End S.

Print Assumptions usedin_arg.
Print Assumptions usedin_deep.
Print Assumptions usedin_applied.
Print Assumptions usedin_let.

(** Nested sections, where a variable of the inner one depends on a constant
    of the outer one. *)

Section Outer.
  Variable o : nat.
  Definition ko := o + 1.
  Section Inner.
    Variable i : ko = ko.
    Definition ki := (i, ko).
    Lemma usedin_nested : ki = ki.
    Proof. exact (match bad return ki = ki with end). Qed.
  End Inner.
End Outer.

Print Assumptions usedin_nested.

(** Universe polymorphic section constants. *)

Section P.
  Polymorphic Universe w.
  Polymorphic Variable T : Type@{w}.
  Polymorphic Definition pk := T -> T.
  Polymorphic Lemma usedin_univ : pk = pk.
  Proof. exact (match bad return pk = pk with end). Qed.
End P.

Print Assumptions usedin_univ.
Set Printing Universes.
Print Assumptions usedin_univ.
Unset Printing Universes.

(** A section in a functor, which is instantiated after the discharge. *)

Module Type T. Axiom bad : False. End T.
Module F (X : T).
  Section S.
    Variable u : nat.
    Definition k := u.
    Lemma usedin_functor : k = k.
    Proof. exact (match X.bad return k = k with end). Qed.
  End S.
End F.
Module XI. Axiom bad : False. End XI.
Module FI := F XI.

Print Assumptions FI.usedin_functor.
