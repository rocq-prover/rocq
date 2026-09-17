Module Type T_template.

  Unset Elimination Schemes.

  #[universes(template)]
  Inductive option (A:Type) : Type := None | Some (_:A).

End T_template.

Module M_template.

  #[universes(template=no)]
  Inductive option (A:Type) : Type := None | Some (_:A).

End M_template.

Fail Module FAIL : T_template := M_template.

Module Type T_private.

  Unset Elimination Schemes.

  Inductive Box (A:Type) := box (_:A).

End T_private.

Module M_private.

  Private Inductive Box (A:Type) := box (_:A).

End M_private.

Fail Module FAIL : T_private := M_private.

Module Type T_primitive.

  Unset Elimination Schemes.

  Record Bla := bli {blo:nat}.

End T_primitive.

Module M_primitive.
  Set Primitive Projections.
  Record Bla := bli {blo:nat}.
End M_primitive.

Fail Module FAIL : T_primitive := M_primitive.

Module Type T_primitive2.

  Unset Elimination Schemes.
  Set Primitive Projections.
  Record Bla := bli {blo:nat}.

End T_primitive2.

Module M_primitive2.

  Record Bla := bli {blo:nat}.

End M_primitive2.

Fail Module FAIL : T_primitive2 := M_primitive2.

Module Type T_uniform.

  Unset Elimination Schemes.
  Parameter id : nat -> nat.
  Inductive Bla (n:nat) : Prop := blo (_ : Bla (id n)).

End T_uniform.

Module M_uniform.

  Unset Elimination Schemes.
  Definition id (n:nat) := n.
  Inductive Bla (n:nat) : Prop := blo (_ : Bla n).

End M_uniform.

Fail Module FAIL : T_uniform := M_uniform.
