(* The universes occurring only in the proofs of the opaque obligations of a polymorphic Program
   definition, e.g. those created by the tactic solving them, are private: they do not appear in
   the instances of the obligations, nor in the universes of the definition. *)

Set Universe Polymorphism.
Set Printing Universes.
Unset Transparent Obligations.

#[local] Obligation Tactic := intros; exact (let _ := Type in I).

Program Definition f@{u} (A : Type@{u}) : { B : Type@{u} | True } := exist _ A _.

About f_obligation_1.
Print f.
