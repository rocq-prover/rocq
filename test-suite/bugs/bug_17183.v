Structure atype := Pack1 {asort : Type}.
Structure btype := Pack2 {bsort : Type}.

Definition b2a cT := Pack1 (bsort cT).
Canonical Structure b2a.

Definition myf (aT : btype) (s : bsort aT) := True.

Axiom absurd : forall x, x.
Axiom mylemma : forall (aT : btype),
  (1 = 0 -> True -> myf aT (absurd (asort (b2a aT)))) -> True.

Require Import ssreflect.

Lemma t : True.
eapply mylemma.
move => [].
(* Anomaly "decompose_prod_n_decls: integer parameter must be positive." *)
Abort.
