(** Test that scheme registrations for section variables require #[local]. *)

Axiom foo : Type.

Section S1.
  Variable A : Type.
  Fail #[export] Register Scheme foo as rew_r_dep for A.
  Fail Global Register Scheme foo as rew_r_dep for A.
  #[local] Register Scheme foo as rew_r_dep for A.
End S1.
