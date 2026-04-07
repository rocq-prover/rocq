(* show alternating separators in typeclass debug output; see discussion in PR #868 *)

Parameter foo : Prop.
Axiom H : foo -> foo.

#[global]
Create HintDb foo.

#[global]
Hint Resolve H : foo.
Goal foo.
Typeclasses eauto := debug.
Fail typeclasses eauto 5 with foo.
Abort.

(* Ensure that actions triggered by hints are always preceded by debug output for the hint iself. *)
Parameter bar cls : Prop.
Axiom c : cls.
Axiom hint : cls -> bar.
Hint Resolve c : foo.

Section Resolve.
  Hint Resolve hint : foo.

  Goal bar.
  Proof.
    typeclasses eauto with foo.
  Qed.
End Resolve.

Section ExternApply.
  Hint Extern 0 bar => apply hint : foo.

  Goal bar.
  Proof.
    typeclasses eauto with foo.
  Qed.
End ExternApply.

Section ExternTC.
  Hint Extern 0 bar => let c := constr:(ltac:(typeclasses eauto with foo) :> cls) in exact (hint c) : foo.

  Goal bar.
  Proof.
    typeclasses eauto with foo.
  Qed.
End ExternTC.
