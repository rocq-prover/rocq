From PrintAssumptionsVOK Require file1.

Lemma main : False.
Proof. apply file1.aux. Qed.

Print Assumptions main.

(* A transparent implementation does not make an unavailable signature proof
   accessible, nor does it make the implemented field an axiom. *)
Module Sealed : file1.Signature.
  Definition value : True := I.
End Sealed.
Print Assumptions Sealed.value.
