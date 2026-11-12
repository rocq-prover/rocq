Require Import Setoid.

Example bug
  (cond : bool)
  (Hceq : cond = true)
  (P : forall (x : bool) (Q : bool -> Type), x = true -> Q true)
  :
  P
     cond
     (fun _ => nat -> Prop)
     (match Hceq in (_ = b) return (cond = b) with
      | eq_refl => eq_refl
      end)
     0
  .
Proof.
  Fail rewrite Hceq at 2.
Abort.
