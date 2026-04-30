(* #20847 is about secvars not getting renamed when pushing rel to
   named.

   This test checks that clearing a secvar and renaming some other var
   to reuse the secvar name is correctly handled (which seems
   necessary to handle renaming secvars in the future). *)
Section C.
  Variable n : nat.

  Definition d : n = n := eq_refl.

  Lemma l : n = n.
  Proof.
    revert n; intros []; [ reflexivity | ].
    apply eq_S. Fail apply d.
  Fail Qed.
  Abort.
End C.
