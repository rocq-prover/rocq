Module M.
Definition one := S(O).
Definition two := S(one).
Definition three := S(two).
Definition four := S(three).
Definition five := S(four).
Definition six := S(five).
Definition seven := S(six).
Definition eight := S(seven).
Definition nine := S(eight).
Definition ten := S(nine).
Lemma H : ten = ten. Proof. reflexivity. Qed.

Search (10) in M.
Search (S(10)) in M.

Set Search Mod Unfolding.

Search (10) in M. (* New: H *)
Search (S(10)) in M. (* No new results *)
End M.
