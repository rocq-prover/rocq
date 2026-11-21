(* -*- coq-prog-args: ("-noinit" "-top" "irredundant_prime"); -*- *)
(* The clauses with several premises of the graph are irredundant (the other clauses do not entail
   them) and prime (no premise p + a of a clause c + k <= max(P) has p + a <= max(P \ {p}, c + k - 1)).
   Print Universes shows the clauses of the graph, while Print Universes Subgraph simplifies them
   again. *)

(* p is redundant once x <= v is added, though x is not the conclusion of a clause of premise p:
   c <= max(p, v) is c <= v *)
Universes p x c v.
Constraint p <= x.
Constraint c <= max(p, v).
Constraint x <= v.

(* A clause entailed by a clause added later is removed: c1 <= max(a1, b1) once c1 <= a1 *)
Universes a1 b1 c1.
Constraint c1 <= max(a1, b1).
Constraint c1 <= a1.

(* Through a chain added later: c2 <= max(a2, b2) once c2 <= d2 <= a2 *)
Universes a2 b2 c2 d2.
Constraint c2 <= max(a2, b2).
Constraint c2 <= d2.
Constraint d2 <= a2.

(* By a clause with several premises: c3 <= max(a3, b3, e3) once c3 <= max(a3, b3) *)
Universes a3 b3 c3 e3.
Constraint c3 <= max(a3, b3, e3).
Constraint c3 <= max(a3, b3).

(* A new clause with several premises entailed by the other ones is not added: c4 <= max(a4, b4)
   with c4 <= d4 and d4 <= max(a4, b4) *)
Universes a4 b4 c4 d4.
Constraint c4 <= d4, d4 <= max(a4, b4).
Constraint c4 <= max(a4, b4).

(* By two clauses with several premises added later: c5 <= max(a5, b5) once c5 <= max(d5, b5) and
   d5 <= max(a5, b5) *)
Universes a5 b5 c5 d5.
Constraint c5 <= max(a5, b5).
Constraint c5 <= max(d5, b5).
Constraint d5 <= max(a5, b5).

(* After a merge: c6 <= max(p6, q6) is c6 <= q6 when p6 = r6 and r6 <= q6 *)
Universes c6 p6 q6 r6.
Constraint c6 <= max(p6, q6).
Constraint r6 <= q6.
Constraint p6 = r6.

(* The clauses with a single premise are kept: a7 <= c7 is entailed by a7 <= b7 <= c7 *)
Universes a7 b7 c7.
Constraint a7 <= c7.
Constraint a7 <= b7, b7 <= c7.

Print Universes.
