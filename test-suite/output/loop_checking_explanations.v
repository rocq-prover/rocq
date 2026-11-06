(* Explanations of universe inconsistencies: a chain of inequalities when the constraint is
   refuted by a path, otherwise a minimal set of constraints, e.g. with clauses [u <= max(l, k)] *)

Monomorphic Universes p q s t.
Monomorphic Constraint p < q, q <= s, s+2 <= t.
Fail Monomorphic Constraint p = q.
Fail Monomorphic Constraint t <= p.
Fail Monomorphic Constraint t <= p+2.
Fail Monomorphic Constraint t+1 <= max(p+3, q+1).
Fail Monomorphic Constraint p+1 <= p.

Monomorphic Universes r c d.
Monomorphic Constraint r < max(c, d).
Fail Monomorphic Constraint max(c, d) <= r.

Monomorphic Universes x y z w.
Monomorphic Constraint x <= max(y, z), y < w, z < w.
Fail Monomorphic Constraint w <= x.

Monomorphic Universes e f g h.
Monomorphic Constraint e < max(g, f), f < max(g, e), g <= h.
Fail Monomorphic Constraint h <= e.

Monomorphic Universes m n o.
Monomorphic Constraint m < max(o, n), o <= max(m, n).
Fail Monomorphic Constraint n < max(o, m).
