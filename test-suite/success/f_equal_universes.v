(* f_equal states the equalities of the arguments at a fresh universe: stating them at the
   universe of the arguments equated it with the universe of the function, here the default
   universe of the template inductive list, and so g1 with g2 *)

Universes g1 g2.

Lemma foo (X Y : Type@{g1}) (H : X = Y) : list X = list Y.
Proof. f_equal. exact H. Qed.

Lemma foo2 (X Y : Type@{g2}) (H : X = Y) : list X = list Y.
Proof. f_equal. exact H. Qed.

(* g1 and g2 are still unrelated *)
Constraint g1 < g2.
