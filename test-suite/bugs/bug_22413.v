Module MultipleFrozenModes.
  Class Foo (x y : nat).

  Global Instance foo_10_10 : Foo 10 10 := {}.

  Global Hint Mode Foo = - : typeclass_instances.

  Goal exists y, Foo 10 y.
  Proof. eexists. typeclasses eauto. Qed.

  Global Hint Mode Foo - = : typeclass_instances.

  (* Multiple mode declarations are alternatives: the newer mode must not
     prevent resolution under an older mode. *)
  Goal exists y, Foo 10 y.
  Proof. eexists. typeclasses eauto. Qed.

  (* Conversely, alternatives must not be merged into a more permissive mode:
     neither declared mode allows both evars to be instantiated. *)
  Goal exists x y, Foo x y.
  Proof. eexists; eexists. Fail typeclasses eauto. Abort.
End MultipleFrozenModes.

Module PermissiveAlternative.
  Class C (n : nat).

  Global Instance c_1 : C 1 := {}.

  Global Hint Mode C ! : typeclass_instances.
  Global Hint Mode C = : typeclass_instances.

  (* Although the newest mode freezes the evar, the older [!] mode permits
     resolution because the evar is not at the head of the argument. *)
  Goal exists n, C (S n).
  Proof. eexists. typeclasses eauto. Qed.
End PermissiveAlternative.

Module NonmatchingAlternative.
  Class C (n : nat).

  Global Instance c_0 : C 0 := {}.

  Global Hint Mode C + : typeclass_instances.
  Global Hint Mode C = : typeclass_instances.

  (* The [+] mode does not match an evar and must not make the matching [=]
     mode more permissive. *)
  Goal exists n, C n.
  Proof. eexists. Fail typeclasses eauto. Abort.
End NonmatchingAlternative.

Module StrictResolution.
  #[local] Set Typeclasses Strict Resolution.

  Class C (x y : nat).

  Global Instance c_0_1 : C 0 1 := {}.

  Global Hint Mode C = - : typeclass_instances.
  Global Hint Mode C - = : typeclass_instances.

  (* The second mode would permit the first evar to be instantiated, but Strict
     Resolution takes precedence over every matching mode alternative. *)
  Goal exists x, C x 1.
  Proof. eexists. Fail typeclasses eauto. Abort.

  Goal C 0 1.
  Proof. typeclasses eauto. Qed.
End StrictResolution.

Module ExternModes.
  Class C (n : nat).

  Global Instance c_0 : C 0 := {}.
  Global Hint Extern 0 (C _) => exact c_0 : typeclass_instances.

  Global Hint Mode C + : typeclass_instances.

  Goal exists n, C n.
  Proof. eexists. Fail typeclasses eauto. Abort.

  Global Hint Mode C = : typeclass_instances.

  (* Mode [=] gates the extern hint but does not restrict the tactic run by
     that hint, so [exact c_0] may instantiate the query evar. *)
  Goal exists n, C n.
  Proof. eexists. typeclasses eauto. Qed.
End ExternModes.
