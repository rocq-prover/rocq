(* f_equal states the equalities of the arguments at a fresh universe: stating them at the
   universe of the arguments equated it with the universe of the function, here the default
   universe of the template inductive list, and so g1 with g2 *)

Unset Universe Polymorphism.

Universes g1 g2.

Lemma foo (X Y : Type@{g1}) (H : X = Y) : list X = list Y.
Proof. f_equal. exact H. Qed.

Lemma foo2 (X Y : Type@{g2}) (H : X = Y) : list X = list Y.
Proof. f_equal. exact H. Qed.

(* g1 and g2 are still unrelated *)
Constraint g1 < g2.

(* The fresh universes of f_equal are internal: in a polymorphic proof they are set to their lower
   bound, here g, instead of becoming universe parameters (as in Stdlib's PairUsualDecidableType) *)
Universe g.
Parameter A : Type@{g}.
Polymorphic Definition pe (x y a b : A) (H : x = y) (H' : a = b) : (x, a) = (y, b).
Proof. f_equal; assumption. Defined.
Check pe@{}.
