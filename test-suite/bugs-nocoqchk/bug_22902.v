(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

Module Type T.
  Universe u v.
  Constraint u < v.
  Symbol T : Type@{u} -> Type@{v}.
  Rewrite Rule r := T Type => Type@{u}.
End T.
Module Import M : T.
  Definition T (x : Type@{T.u}) := Type@{T.u}.
End M.
