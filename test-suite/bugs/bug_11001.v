Section Section.

Context (c : false = true).

Create Rewrite HintDb db.
Hint Rewrite c : db.

Lemma d : true = false.
Proof. symmetry; exact c. Qed.

Hint Rewrite d : db.

Goal false = false.
Proof.
autorewrite with db.
match goal with |- true = true => idtac end.
Abort.

Goal false = false.
Proof.
clear c.
autorewrite with db.
reflexivity.
Qed.

End Section.
