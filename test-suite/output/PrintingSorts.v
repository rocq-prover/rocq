Sort s.
Axiom S : Type@{s;Set}.
Axiom T : Type.

(* Without Printing Sorts or Printing Universes *)
Check S.
Check T.

(* With Printing Sorts: sort variables visible, universe levels anonymized *)
Set Printing Sorts.
Check S.
Check T.
Unset Printing Sorts.

(* With Printing Universes: full names *)
Set Printing Universes.
Check S.
Check T.
Unset Printing Universes.

(* Universe-polymorphic definitions and inductives *)
#[universes(polymorphic)] Definition pid@{u} (A : Type@{u}) (a : A) := a.
#[universes(polymorphic)] Inductive plist@{u} (A : Type@{u}) := pnil | pcons (a : A) (l : plist A).

Check pid.
Check plist.

Set Printing Sorts.
Check pid.
Check @pid.
Check plist.
Check pnil.
Check pcons.
Unset Printing Sorts.

Set Printing Universes.
Check pid.
Check plist.
Unset Printing Universes.

(* Sort-polymorphic definitions and inductives *)
#[universes(polymorphic)] Definition spid@{s;u} (A : Type@{s;u}) (a : A) := a.
#[universes(polymorphic)] Inductive sbox@{s;u} (A : Type@{s;u}) := spack (a : A).

Check spid.
Check sbox.

Set Printing Sorts.
Check spid.
Check @spid.
Check sbox.
Check spack.
Unset Printing Sorts.

Set Printing Universes.
Check spid.
Check @spid.
Check sbox.
Check spack.
