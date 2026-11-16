Set Primitive Projections.
Set Universe Polymorphism.

Inductive foo@{s;l|} : Univ@{s;Set} := { Foo : foo }.

Check foo_rect_nodep@{Type;Set Set}.
Check foo_ind_nodep@{Prop;Set}.
Fail Check foo_rect_nodep@{SProp;Set Set}.

Inductive R : SProp := { r : R }.

Check R_sind.
Fail Check R_rect.
