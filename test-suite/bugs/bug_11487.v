Parameter parameters: Type.
Parameter mem: parameters -> Type.
Parameter rel: forall {p: parameters}, mem p -> mem p -> Prop.

Section Foo.
  Context (p: parameters).

  Lemma Proper_load: forall (m: mem p), rel m m. Admitted.

  Goal forall (p: parameters) (m: mem p), rel m m.
  Proof.
    clear p.
    intros p m.
    Fail Check Proper_load.
  Abort.
End Foo.
