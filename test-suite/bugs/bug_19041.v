Inductive T : bool -> SProp := .

Goal forall (x:T true) (y:T false), match x return bool with end = match y return bool with end.
Proof.
  intros.
  Fail reflexivity.
  match goal with |- ?a = ?b => vm_cast_no_check (eq_refl a) end.
  Fail Qed.
Abort.
