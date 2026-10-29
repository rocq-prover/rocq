(* Printing a global whose polymorphic universe context, coming from a
   section, identifies a universe with Set or bounds it by Set. *)
Set Universe Polymorphism.
Set Printing Universes.

Section S.
  Universe u.
  Constraint u = Set.
  Definition foo : Type@{u} := nat.
End S.

Print foo.
About foo.
Check foo@{Set}.

Section S2.
  Universe v.
  Constraint v <= Set.
  Definition goo : Type@{v} := nat.
End S2.

Print goo.
About goo.
