(* Hint patterns are built lazily, so they must not depend on how evars
   happen to be instantiated at that point, which backtracking may undo. *)

Inductive sb_tag := sb_L | sb_R.
Definition sb_left := sb_L.
Definition sb_right := sb_R.

Class SBTarget (t : sb_tag) := {}.
Class SBChoice (t : sb_tag) := { sb_choice : SBTarget t }.

#[local] Instance sb_pick_left : SBChoice sb_left | 1 :=
  {| sb_choice := Build_SBTarget sb_left |}.
#[local] Instance sb_pick_right : SBChoice sb_right | 2 :=
  {| sb_choice := Build_SBTarget sb_right |}.

Definition sb_consume `{SBTarget sb_right} : Prop := True.

Lemma sb_test : let i := sb_choice in sb_consume.
Proof. exact I. Qed.

Module Ctor.
Inductive sb_tag := sb_L | sb_R.
Definition sb_left := sb_L.
Definition sb_right := sb_R.

Class SBTarget (t : sb_tag) := {}.
Class SBChoice (t : sb_tag) := { sb_choice : SBTarget t }.

#[local] Instance sb_pick_left : SBChoice sb_L | 1 :=
  {| sb_choice := Build_SBTarget sb_L |}.
#[local] Instance sb_pick_right : SBChoice sb_R | 2 :=
  {| sb_choice := Build_SBTarget sb_R |}.

Definition sb_consume `{SBTarget sb_R} : Prop := True.

Lemma sb_test : let i := sb_choice in sb_consume.
Proof. exact I. Qed.
End Ctor.
