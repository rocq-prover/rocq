Axiom R : Set.

Module Type Typ.
  Parameter Inline(10) t : Type.
End Typ.

Module Make_UDTF (M:Typ).
  Include M.
End Make_UDTF.

Module R_as_UBE.
 Definition t := R.
End R_as_UBE.

Module FOO := Make_UDTF R_as_UBE.

Module BAR.
 Include FOO.
End BAR.

Definition boom := BAR.t.
