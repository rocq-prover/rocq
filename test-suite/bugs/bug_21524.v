(* this would create a module that could only be imported when univ poly is on *)

Module M.
  #[local] Set Universe Polymorphism.
  #[export] Set Polymorphic Inductive Cumulativity.
End M.

Import M.
