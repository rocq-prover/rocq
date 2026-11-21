(* A canonical instance whose value is the projection as a function (a
   partial application of its compatibility constant) applies to the
   projection of a record. *)
Set Primitive Projections.
Record fn := Fn { app : nat -> nat; fn_prf : app 0 = 0 }.
Record sub := Sub { val_of : fn -> nat -> nat }.
Unset Primitive Projections.
Canonical fn_sub := Sub (fun f => app f).
Check fun (f : fn) => (eq_refl : val_of _ f = app f).
Check fun (f : fn) (g : fn -> nat -> nat) (H : forall s x, val_of s x = g x) => (H _ f : app f = g f).
