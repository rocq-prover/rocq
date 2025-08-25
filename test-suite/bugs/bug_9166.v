Set Warnings "+deprecated".

#[deprecated(since = "X", note = "Y")]
Abbreviation bar := option.

Definition foo (x: nat) : nat :=
  match x with
  | 0 => 0
  | S bar => bar
  end.
