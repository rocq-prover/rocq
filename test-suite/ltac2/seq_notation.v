Require Import Ltac2.Ltac2.

(* tests that the seq subterms are parsed in the right order, and
   tupled in the right order. *)
Ltac2 Notation "foo" x(seq(constr,ident,thunk(tactic(0)))) y(ident) := (x,y).

Ltac2 bar () : (constr * ident * (unit -> unit)) * ident := foo 0 x intros z.
