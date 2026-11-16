#[sealed] Definition sdef := 0.

Check sdef:nat.
Fail Check eq_refl : sdef = 0.

#[defined] Definition ddef := 0.

Check eq_refl : ddef = 0.

#[sealed] Program Definition sprogdef : nat := _.
Next Obligation. exact 0. Defined.

Check sprogdef:nat.
Fail Check eq_refl : sprogdef = 0.
Check eq_refl : sprogdef_obligation_1 = 0.

#[sealed] Fixpoint sfix (n:nat) := match n with 0 => 0 | S k => sfix k end.

Check sfix : nat -> nat.
Fail Check eq_refl : sfix 0 = 0.

#[sealed] Program Fixpoint sprogfix (n:nat) : nat := match n with 0 => 0 | S k => sprogfix _ end.
Next Obligation.
  exact (fun _ k _ => k).
  Fail Qed.
Defined.

Check sprogfix : nat -> nat.
Fail Check eq_refl : sprogfix 0 = 0.

Class C := CC {}.

#[sealed] Instance inst : C := {}.

Definition useinst : C := _.

Check eq_refl : useinst = inst.
Fail Check eq_refl : useinst = CC.

(* commands which open a proof don't support "sealed" because the proof has its own terminator *)

Fail #[sealed] Definition notsuppdef : nat.
Fail #[defined] Definition notsuppdef : nat.

Fail #[sealed] Fixpoint notsuppfix (n:nat) : nat.

Fail #[sealed] Fixpoint notsuppfix1 (n:nat) := match n with 0 => 0 | S k => notsuppfix2 k end
    with notsuppfix2 (n:nat) : nat.

Fail #[sealed, refine] Definition notsupprefine : nat := _.
