Class Subst := subst_instance : unit.
Arguments subst_instance _ : clear implicits.

Module Type Term.
  Parameter Inline subst_local : Subst.
End Term.

Module Environment (T : Term).
#[global] Existing Instance T.subst_local.
End Environment.

#[global] Declare Instance subst_global : Subst.

Module TemplateTerm.
Definition subst_local := subst_instance _.
End TemplateTerm.

Module Env := Environment TemplateTerm.

(* Check that the TC instance does not produce the inlined version but
   produces instead the reference from the module. *)

Lemma test : subst_instance _ = tt.
Proof.
match goal with
[ |- @subst_instance TemplateTerm.subst_local = tt ] =>
  idtac
end.
(* We used to have [@subst_instance (@subst_instance subst_global) = tt] *)
Abort.
