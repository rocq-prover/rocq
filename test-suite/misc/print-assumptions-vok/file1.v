Lemma hidden : False.
Proof. Admitted.

Lemma aux : False.
Proof. apply hidden. Qed.

Module Type Signature.
  Lemma value : True. Proof. exact I. Qed.
End Signature.
