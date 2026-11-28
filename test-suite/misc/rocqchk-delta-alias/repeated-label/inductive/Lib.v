(* The forged copy gives the inductive type J the label I, and the name of I
   in its automaton, where J holds its own name. J keeps its type name J, so
   the clash is on the block's own label: a second use of a label among the
   constants and inductive types. The environment then keeps the last block
   labelled I, which is J. proof was checked against the first block, and
   its type then has no constructor. *)

Unset Elimination Schemes.

Inductive I : Prop := i.

Definition proof : I := i.

Inductive J : Prop := .
