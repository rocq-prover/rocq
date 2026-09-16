Module Type T. Parameter a : bool. End T.

Module F (X : T).
  Module Inner. Definition c := X.a. End Inner.
  Module Copy. Include Inner. End Copy.
  Module Wrap. Module Alias := Copy. End Wrap.
End F.

Module A. Definition a := true.  Include F. End A.
Module B. Definition a := false. Include F. End B.

Fail Definition confused : A.Wrap.Alias.c = B.Wrap.Alias.c := eq_refl.
