Module Type Universe.
Parameter U : nat.
End Universe.

Module Univ_prop (U : Universe).
Include U.
End Univ_prop.

Module Monad (U : Universe).
Module UP := Univ_prop U.
End Monad.

Module Rules (U : Universe).
Module MP := Monad U.
Include MP.
Import UP.
Definition M := UP.U.    (* anomaly here *)
End Rules.
