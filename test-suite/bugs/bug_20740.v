Structure C := {
  Ty :> Type;

  coercion_to_unit : Ty -> unit
}.

#[reversible]
Coercion coercion_to_unit : Ty >-> unit.

Structure A_ := {
  term_a : unit
}.
Definition A : Type := {| coercion_to_unit := term_a |}.
Identity Coercion coe_A : A >-> Ty.
Canonical a (x : unit) := {| term_a := x |}.

Structure B_ := {
  term_b : unit
}.
Definition B : Type := {| coercion_to_unit := term_b |}.
Identity Coercion coe_B : B >-> Ty.
Canonical b (x : unit) := {| term_b := x |}.

Check (fun x : unit => x : A).
Check (fun x : unit => x : B).

Check (fun x : A => x : B). (* this should work *)
