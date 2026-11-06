(* The universes of the side effects of [abstract] are demoted, i.e. global in the universe
   state of the proof, and local again when the side effects are inlined at Qed. Declaring
   global universes in the proof rebases its universe state on the new global graph: the
   demoted universes must stay demoted there. *)
Unset Universe Polymorphism.
Set Printing Universes.
Definition T := Type.
Lemma foo : T.
Proof.
  unfold T.
  abstract (exact (Type -> Type)).
  Monomorphic Universe w.
Qed.
Print foo.
Print Universes Subgraph (T.u0 foo.u0 foo.u1).
Lemma foo2 : Type * Type.
Proof.
  split; [abstract exact Type|].
  (* The universes of the side effect are used in the rest of the proof *)
  let T := type of foo2_subproof in pose (X := T).
  Monomorphic Universe w2.
  exact (X : Type).
Qed.
Print foo2.
Print Universes Subgraph (foo2.u0 foo2.u1 foo2.u2 foo2.u3).
(* Side effects inlined by ltac:(...) *)
Definition baz : Type := ltac:(abstract exact Type).
Print baz.
Print Universes Subgraph (baz.u0).
(* A nested command is run by the STM in the environment before the proof, without the side
   effects of the proof: they stay demoted in the proof *)
Lemma foo3 : Type * Type.
Proof.
  split; [abstract exact Type|].
  Definition bar := Type.
  exact Type.
Qed.
Print foo3.
Print bar.
Print Universes Subgraph (foo3.u0 foo3.u1 foo3.u2 foo3.u3 bar.u0).
Set Nested Proofs Allowed.
Lemma foo4 : Type.
Proof.
  abstract (exact Type).
  Lemma nested : Type.
  Proof. exact Type. Qed.
Qed.
Print foo4.
Print nested.
