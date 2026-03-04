Module Type S.
Fail Primitive float := #float64_type.
Fail Register bool as kernel.ind_bool.

Module M.
Fail Primitive float := #float64_type.
Fail Register bool as kernel.ind_bool.
End M.

End S.

Module Type T.
End T.

Module F(X : T).
Fail Primitive float := #float64_type.
Fail Register bool as kernel.ind_bool.
End F.

Module Type G(X : T).
Fail Primitive float := #float64_type.
Fail Register bool as kernel.ind_bool.
End G.

Module M.

Primitive string := #string_type.
Register bool as kernel.ind_bool.

End M.

(* The commands below work but create an alias, so no double-registration *)

Module N1 := M.
Module N2.
Include M.
End N2.

Module Type U.
Include M.
End U.

Declare Module N3 : U.
