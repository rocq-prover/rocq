Class Need := {  }.

Hint Extern 0 Need => abstract constructor : typeclass_instances.

Definition satisfy (H : Need) : unit := let 'B := H in tt.

Section Foo.

Context {X Y : satisfy _ = tt}.
(* Anomaly "Constant Top.instance_subproof does not appear in the environment." *)

End Foo.
