  Lemma inv_acc_strong E N P :
    ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ ▷ P ∗ ∀ E', ▷ P ={E',↑N ∪ E'}=∗ True.
  Proof.
    iIntros (?) "Hinv".
    (* `rocq wc` got confused by tactics like these, ending in "Proof" *)
    iPoseProof (inv_acc (↑ N) N with "Hinv") as "H"; first done.
    rewrite difference_diag_L.
    iPoseProof (fupd_mask_frame_r _ _ (E ∖ ↑ N) with "H") as "H"; first set_solver.
    rewrite left_id_L -union_difference_L //. iMod "H" as "[$ H]"; iModIntro.
    iIntros (E') "HP".
    (* also works with non-ascii names: *)
    iPoseΔProof (fupd_mask_frame_r _ _ E' with "(H HP)") as "H"; first set_solver.
    by rewrite left_id_L.
  Qed.
