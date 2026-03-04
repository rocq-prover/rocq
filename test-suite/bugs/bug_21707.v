Module Type T.
  Parameter t : Type.
End T.

Module F(X:T with Definition t := nat).
End F.

Module N.
  Definition t : Type := nat.
End N.

(** Check that the type of [X:T with Definition t := nat] is
    the largest type rather than the smallest type, i.e. it
    has field [Definition t : Type := nat] rather than
    [Definition t : Set := nat.] *)
Module FN := F N.
