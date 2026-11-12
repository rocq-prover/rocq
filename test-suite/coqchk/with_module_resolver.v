(* The resolver of a module can give a field of a submodule another
   canonical name than the submodule's own resolver does: in
   S with Module X := B below, the resolver of the result keeps S's alias
   X.c -> Q.c (XT includes Q), while the resolver of X makes X.c B.c.
   rocqchk must accept this, since B.c := Q.c. *)

Module Q.
  Definition c : bool := true.
End Q.

Module Type XT.
  Include Q.
End XT.

Module Type S.
  Declare Module X : XT.
End S.

Module B.
  Definition c : bool := Q.c.
End B.

Module Type S2 := S with Module X := B.

Module M : S with Module X := B.
  Module X := B.
End M.

Module F (P : S with Module X := B).
End F.
