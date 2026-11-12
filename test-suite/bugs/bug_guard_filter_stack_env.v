Inductive True2 : Prop := I2 : (False -> True2) -> True2.

Inductive Eq (A : Prop) : forall (B : Prop) (L : Prop := True2), Prop := Eq_refl : Eq A A.

Fail Fixpoint f (e : Eq True2 (False -> True2)) (x : True2) {struct x} : False :=
  match x with
  | I2 H =>
    f e (match e in Eq _ Y return (nat -> nat) -> Y -> True2 with
         | Eq_refl _ => fun _ y => y
         end (fun n => n) H)
  end.
