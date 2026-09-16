(* An "only printing" declaration at a level other than the recorded one was
   rejected when the other was "only printing" too, accepted when it was a
   parsing one.  Both are accepted now. *)

Module OnlyPrintingThenParsing.
  Notation "!!" := False (at level 0, only printing).
  Notation "!!" := False (at level 1).
End OnlyPrintingThenParsing.

Module OnlyPrintingThenOnlyPrinting.
  Notation "!!" := False (at level 0, only printing).
  Notation "!!" := False (at level 1, only printing).
End OnlyPrintingThenOnlyPrinting.
