Module Type S.
#[global] Create HintDb bugdb.
End S.

Module F(X : S).

#[global] Hint Immediate true : bugdb.

End F.

Module M.
End M.

Module Import N := F(M). (* anomaly because bugdb is actually not declared *)
