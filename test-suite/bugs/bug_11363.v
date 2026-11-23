Require Import Corelib.derive.Derive.

Class Foo {A B C D : Type} (x : A) := {}.

Derive foo in (Foo foo) as bar.
Proof.
  constructor.
  Unshelve.
  exact I.
  Unshelve.
  all: exact nat.
Qed.
