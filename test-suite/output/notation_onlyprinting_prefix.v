(* Later notations sharing a prefix take their default levels from the prefix
   table, and are checked against it for factorization.  A declaration with no
   parsing rule used to be registered there too, and its argument levels then
   leaked into the grammar of a later parsing notation.

   The "only printing" declaration below puts its right argument at level 16.
   The parsing rule after it asks for no associativity at level 70, which means
   both arguments at the next level.  It used to get level 16 on the right
   instead, so "0 == 1 + 1" parsed as "(0 == 1) + 1" and did not typecheck. *)

Parameter expr : Type.
Parameter Ebinop : nat -> expr -> expr -> nat -> expr.
Declare Scope expr_scope.
Delimit Scope expr_scope with expr.
Notation "a1 == a2" := (Ebinop 1 a1%expr a2%expr 0)
  (only printing, a2 at level 16, left associativity, at level 17,
   format "'[hv  ' a1  '/' ==  a2 ']'") : expr_scope.

Declare Scope test_bool_scope.
Notation "x == y" := (Nat.eqb x y) (at level 70, no associativity) : test_bool_scope.
Open Scope test_bool_scope.

(* The right argument is parsed at the next level, so the addition is grouped
   inside it.  The warning above reports the recorded level, still 17. *)
Check (0 == 1 + 1).
