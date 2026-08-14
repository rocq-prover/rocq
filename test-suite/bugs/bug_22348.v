From Corelib Require Extraction.

Record box : Type := make_box {
  value : nat
}.

Extraction Implicit make_box [1].

Definition make_box_value : box := make_box 1.
Extraction TestCompile make_box_value.

Definition match_box (b : box) : nat :=
  match b with
  | make_box _ => 0
  end.
Extraction TestCompile match_box.

Definition use_box_value : nat := value (make_box 1).
Fail Extraction TestCompile use_box_value.

Record pbox (A : Type) : Type := make_pbox {
  pvalue : A
}.

Extraction Implicit make_pbox [2].

Definition make_pbox_value : pbox nat := make_pbox nat 1.
Extraction TestCompile make_pbox_value.

Definition match_pbox (b : pbox nat) : nat :=
  match b with
  | make_pbox _ _ => 0
  end.
Extraction TestCompile match_pbox.
