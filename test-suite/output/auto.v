(* testing info_*/debug auto/eauto *)

Goal False \/ (True -> True).
Proof.
Succeed info_auto.
Succeed debug auto.
Succeed info_eauto.
debug eauto.
Defined.

Goal True.
Proof.
info_trivial.
Defined.
