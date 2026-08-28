Class C (x y : nat).

Global Hint Extern 0 (C _ _) => idtac "extern called"; fail : typeclass_instances.

Global Hint Mode C + + : typeclass_instances.

Goal exists x y, C x y.
Proof.
  eexists; eexists.
  Fail typeclasses eauto.
Abort.

Global Hint Mode C = - : typeclass_instances.
Global Hint Mode C - = : typeclass_instances.

Goal exists x y, C x y.
Proof.
  eexists; eexists.
  (* Although both mode declarations match with distinct restrictions, the
     extern hint is run only once because it does not use those restrictions. *)
  Fail typeclasses eauto.
Abort.
