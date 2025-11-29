Class Need := {  }.

Hint Extern 0 Need => abstract constructor : typeclass_instances.

Definition satisfy (H : Need) : unit := tt.

(* Check that various declaration paths correctly register abstracted constants *)

Definition defdef (n : nat) : unit := satisfy _.

Fixpoint fixdef (n : nat) : unit :=
match n with
| 0 => tt
| S n => match satisfy _ with tt => fixdef n end
end.

(* These two are still broken: *)
(* Axiom axmdef : satisfy _ = tt. *)
(* Program Definition progdef := satisfy _. *)
