Polymorphic Record foo@{s;u|} (x : Type@{s;u}) := {}.

Set Universe Polymorphism.

Module Type A. Axiom A@{i} : Type@{i}. Axiom B : foo A. End A.
Module B <: A. Axiom A@{i} : Prop. Axiom B : foo A. Fail End B.
