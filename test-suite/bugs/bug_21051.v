Module Type T.
Parameter n : bool.
End T.

Module M.
Definition n := true.
End M.

Module M'.
Definition n := false.
End M'.

Module MAKE.

Module FUN (E : T).

Module F.
Definition bug := E.n.
End F.

Module G := F.

End FUN.

End MAKE.

Include MAKE.

Module RES := FUN M.
Module RES' := FUN M'.

Lemma foo : RES.G.bug = RES'.G.bug.
Proof.
Fail reflexivity. (* Was succeeding, allowing to derive False with the code below. *)
Abort.

(*
Lemma foo0 : RES.G.bug = true.
Proof.
reflexivity.
Qed.

Lemma foo1 : RES'.G.bug = false.
Proof.
reflexivity.
Qed.

Lemma unsound : False.
Proof.
assert (true = false); [|congruence].
rewrite <- foo0; rewrite <- foo1; apply foo.
Qed.

Print Assumptions unsound.
*)
