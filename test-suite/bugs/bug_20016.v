Set Definitional UIP.

Inductive eq {A} (x : A) : A -> SProp := refl : eq x x.

Definition cast {A B} (e : eq A B) (x : A) : B :=
match e in eq _ C return C with refl _ => x end. (* Bad case inversion (maybe a bugged tactic). *)

Polymorphic Definition pcast@{q|u|+} {A B:Type@{q|u}} (e : eq A B) (x : A) : B :=
  match e in eq _ C return C with refl _ => x end.

Definition cast0 := @pcast@{SProp|Set}.

Definition cast0' := Eval lazy in cast0.
