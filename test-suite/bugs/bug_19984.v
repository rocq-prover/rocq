Module Type S. End S.

Module N. End N.

Module Type T.

Declare Module F(X : S) : S.

End T.

Module F0 (X : S).
Definition n := 2. (* dummy value to sanity-check subtyping *)
End F0.

(* This works, note the <: *)

Module M_ok <: T with Module F := F0.

Module F(X : S).
Definition m := 1.
Definition n := m + m.
End F.

End M_ok.

Module FF_ok := M_ok.F.
Module MM_ok := FF_ok(N).

(* This does not after sealing *)

Module M_ko : T with Module F := F0.

Module F(X : S).
Definition m := 1.
Definition n := m + m.
End F.

End M_ko.

Module FF_ko := M_ko.F.
Module MM_ko := FF_ko(N). (* Error: Application of a functor with too few arguments. *)
