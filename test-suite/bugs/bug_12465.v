(* Two "only printing" declarations for the same notation string, differing
   only in the entry of their first argument, used to be rejected.  Neither
   adds a parsing rule, so there is no grammar to disagree about. *)

Axiom funspec : forall {A B} T (pre : T -> A) (post : T -> B), Prop.

Notation "'WITH' x : A  'PRE'  [ ] P 'POST' [ ] Q" :=
  (funspec _ (fun x : A => P) (fun x : A => Q))
    (at level 200, x ident, P at level 100, Q at level 100, only printing).

Notation "'WITH' x : A  'PRE'  [ ] P 'POST' [ ] Q" :=
  (funspec _ (fun x : A => P) (fun x : A => Q))
    (at level 200, x strict pattern at level 9, P at level 100, Q at level 100,
     only printing).
