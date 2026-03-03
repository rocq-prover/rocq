Inductive sFalse : SProp := .

Definition f (x:sFalse) := match x return nat -> nat with end.

Fail Definition bli : (fun x : sFalse => f x 0) = (fun x : sFalse => f x 1)
  := eq_refl.

(* use unsafe tac to ensure it's not just fixed in the higher layers *)
Definition bli : (fun x : sFalse => f x 0) = (fun x : sFalse => f x 1).
Proof.
  match goal with |- ?l = _ => exact_no_check (eq_refl l) end.
  Fail Qed.
Abort.

(* definitional uip version *)
Set Definitional UIP.
Inductive seq {A} (a:A) : A -> SProp :=
  srefl : seq a a.

Definition F {x y:nat} (e:seq x y) := match e return nat -> nat with srefl _ => fun x => x end.

Fail Definition bli (x y:nat) (e:seq x y) : F e 0 = F e 1 := eq_refl.

Definition bli (x y:nat) (e:seq x y) : F e 0 = F e 1.
Proof.
  match goal with |- ?l = _ => exact_no_check (eq_refl l) end.
  Fail Qed.
Abort.
