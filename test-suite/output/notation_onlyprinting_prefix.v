(* Later notations sharing a prefix take their default levels from the prefix
   table, which used to hold declarations with no parsing rule too.

   The "only printing" declaration below puts its right argument at level 16.
   The parsing rule after it asks for no associativity at level 70, so both
   arguments at the next level.  It used to get level 16 on the right instead,
   and "0 == 1 + 1" parsed as "(0 == 1) + 1". *)

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

Check (0 == 1 + 1).
