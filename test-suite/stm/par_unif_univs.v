(* -*- coq-prog-args: ("-async-proofs-tac-j" "1"); -*- *)

(* The single tactic worker solves both goals, each one starting from the
   state of the main process. The unification level of [Type] it creates for
   the first goal must not have the same name as the one for the second goal,
   otherwise the main process merges [ℓ <= u] and [u < ℓ]. *)

Universe u.

Lemma par_unif_univs : True /\ 0 = 0.
Proof.
  split.
  par: abstract (first [exact ((fun (A : Type) => let _ : Type@{u} := A in I) nat)
                       | exact ((fun (A : Type) (_ : A) => @eq_refl nat 0) Type@{u} nat)]).
Qed.
