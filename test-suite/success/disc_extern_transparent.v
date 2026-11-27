(* Hint Extern patterns are matched syntactically, so discrimination nets
   must keep a wildcard for transparent constants and projections that such
   patterns mention, instead of resolving them through their bodies. *)

Definition T (n : nat) := n = n.
Definition W (n : nat) := T n.
Definition U (n : nat) := W n.

Class C (P : Prop) := c : P.

Hint Extern 0 (C (T _)) => exact (eq_refl _) : typeclass_instances.

Goal C (T 3). Succeed typeclasses eauto. Abort.
Goal C (W 3). Fail typeclasses eauto. Abort.
Goal C (U 3). Fail typeclasses eauto. Abort.

Class D (P : Prop) := d : P.
Hint Extern 0 (D (W _)) => exact (eq_refl _) : typeclass_instances.
Goal D (W 3). Succeed typeclasses eauto. Abort.
Goal D (T 3). Fail typeclasses eauto. Abort.
Goal D (U 3). Fail typeclasses eauto. Abort.

Class E (P : Prop) := e : P.
Hint Extern 0 (E (and (T _) (W _))) => split; exact (eq_refl _) : typeclass_instances.
Goal E (and (T 1) (W 2)). Succeed typeclasses eauto. Abort.
Goal E (and (U 1) (W 2)). Fail typeclasses eauto. Abort.

Set Primitive Projections.
Record R := { f : nat -> Prop }.
Definition r := {| f := fun n => n = n |}.
Class F (P : Prop) := ff : P.
Hint Extern 0 (F (f r _)) => exact (eq_refl _) : typeclass_instances.
Goal F (f r 3). Succeed typeclasses eauto. Abort.
Goal F (r.(f) 3). Succeed typeclasses eauto. Abort.
Goal F (T 3). Fail typeclasses eauto. Abort.

Hint Extern 0 (F (f _ 4)) => exact (eq_refl _) : typeclass_instances.
Goal F (f r 4). Succeed typeclasses eauto. Abort.

Create HintDb tdb discriminated.
Hint Extern 0 (T _) => reflexivity : tdb.
Hint Extern 0 (f r _) => reflexivity : tdb.
Goal T 5. Succeed solve [auto with tdb nocore]. Abort.
Goal W 5. Fail solve [auto with tdb nocore]. Abort.
Goal f r 5. Succeed solve [auto with tdb nocore]. Abort.
Goal r.(f) 5. Succeed solve [auto with tdb nocore]. Abort.
Goal T 5. Succeed solve [typeclasses eauto with tdb]. Abort.
Goal f r 5. Succeed solve [typeclasses eauto with tdb]. Abort.
