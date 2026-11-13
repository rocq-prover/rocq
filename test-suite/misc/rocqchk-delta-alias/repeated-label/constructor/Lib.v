(* The forged copy names the constructor k of K c, the label of the
   constant before it: a second use of a label among the constants,
   inductive types and constructors, which coqc never writes. The block's
   own label is K, so only the names of its constructors give the second
   use. *)

Unset Elimination Schemes.

Inductive unit : Set := tt.

Definition c : unit := tt.

Inductive K : Prop := k.
