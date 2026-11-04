Section MySection.
  Context {T} (p:T).
  Axiom ax : p = p.
  Definition def := ax.
  Lemma lem : def = ax.
  Proof.
    reflexivity.
  Qed.

  Section SubSec.

    Variable subv : nat.

    About MySection.
    Print MySection.
    Print SubSec.
  End SubSec.
End MySection.

Module M1.

  Definition a0 := 0.
  Definition a1 := false.

  Module Type T1.

    Parameter b0 : bool.
    Parameter b1 : nat.

    Module M2.
      Definition bb0 : b0 = b0 := eq_refl.
      Definition bb1 : b1 = b1 := eq_refl.

      Print M1.
      Print T1.
      Print M2.
    End M2.
    Print T1.
    Print M2.
  End T1.
  Print M1.
End M1.
