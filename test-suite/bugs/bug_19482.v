Definition foo := nat.
#[global]Typeclasses Opaque foo.
#[global] Opaque foo. (* both succeed happily *)

Definition bar := nat.
#[global] Opaque bar.
#[global] Typeclasses Opaque bar. (* Cannot coerce bar to an evaluable reference. *)
(* I would expect it to succeed, with the same behaviour as for `foo`. *)
