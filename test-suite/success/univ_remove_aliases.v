(* Removing a universe from a universe context keeps the constraints of its kept aliases.
   Here the universes [a] and [b] of the statement are both made equal to [l + 1], for a
   universe [l] of the proof: [a] and [b] become aliases of [l + 1], as [l] cannot be an
   alias of [a - 1]. [l] is private to the proof, and restricting the context of the
   statement to [a] and [b] removes it: the public context must still have [a = b] and
   [1 <= a], or Qed fails with "Local constraints imply new transitive constraints". *)
Set Universe Polymorphism.
Set Printing Universes.
Lemma shifted_aliases@{a b} (A : Type@{a}) (B : Type@{b}) : True.
Proof.
  pose (L := Type@{_}).
  let T := type of L in pose proof (eq_refl : @eq Type@{_} Type@{a} T) as ha.
  let T := type of L in pose proof (eq_refl : @eq Type@{_} Type@{b} T) as hb.
  exact I.
Qed.

(* The public context has [a = b]: the declared universes must imply it *)
Definition ok@{x | Set < x} := shifted_aliases@{x x}.
Fail Definition ko@{x y | Set < x, Set < y} := shifted_aliases@{x y}.

(* The same with many universes in the graph, and many removed ones *)
Monomorphic Universes g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20.

Lemma shifted_aliases_many@{a b} (A : Type@{a}) (B : Type@{b}) : True.
Proof.
  do 30 (pose (X := Type@{_}); clear X).
  pose (L := Type@{_}).
  let T := type of L in pose proof (eq_refl : @eq Type@{_} Type@{a} T) as ha.
  let T := type of L in pose proof (eq_refl : @eq Type@{_} Type@{b} T) as hb.
  exact I.
Qed.

Definition ok_many@{x | Set < x} := shifted_aliases_many@{x x}.
Fail Definition ko_many@{x y | Set < x, Set < y} := shifted_aliases_many@{x y}.
