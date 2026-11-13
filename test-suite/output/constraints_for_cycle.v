(* The constraints between the kept universes are derived through the universes they bound, even
   when none of their clauses has all its premises bounded: x + 2 <= max(b + 1, b0), hence
   a + 2 <= max(b + 1, b0). *)
Universes a b b0 x p.
Constraint a <= x.
Constraint x < max(p, b).
Constraint p < max(x, b0).
Print Universes Subgraph (a b b0).

(* A cycle of weight 0 does not bound its universes: y and q can be raised together with
   y = q + 1, so that c is not bounded by d. *)
Universes c d y q.
Constraint c <= y.
Constraint q < y.
Constraint y <= max(q+1, d).
Print Universes Subgraph (c d).
