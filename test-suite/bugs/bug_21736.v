Set Universe Polymorphism.

Definition foo@{u v} : Type@{v} := Type@{u}.
Register Inline foo.

(* if [typ] is inlined (in the source) the checker rejects bar, I guess because it
   doesn't use the Register Inline hint when doing its own compilation
   but does reuse the compilation of [typ] which did the incorrect inlining. *)
Definition typ@{v u k} := Type@{v} = foo@{u v} :> Type@{k}.

Lemma bar@{v u k|u < v, v < k} : typ@{v u k}.
Proof.
  vm_cast_no_check (@eq_refl Type@{k} Type@{v}).
  Fail Qed.
Abort.

Lemma bar@{v u k|u < v, v < k} : typ@{v u k}.
Proof.
  native_cast_no_check (@eq_refl Type@{k} Type@{v}).
  Fail Qed.
Abort.
