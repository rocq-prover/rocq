Module Type UNIT.
End UNIT.

Module notation (U : UNIT).
  Definition parser (_ : list Byte.byte) : option nat := Some O.
  Definition printer (_ : nat) : option (list Byte.byte) := Some (cons Byte.x61 nil).

  String Notation nat parser printer : nat_scope.
End notation.

Include notation.

Check "foo"%nat.
