(* A declaration that adds no parsing rule has no grammar to agree with, so it
   may be declared at a level other than the one already recorded for its
   notation string (#12465, #12589, see also #6078).

   VST's floyd/Clightnotations.v declares "only printing" "_ == _" and "_ != _"
   at level 17.  ssreflect declares parsing rules for the same strings at 70.
   Loading ssreflect first used to make the VST file fail.  That shape, what
   gets printed, and the errors that remain are pinned in
   output/notation_onlyprinting_level.v.  Here we only check that the
   declarations reaching the level check by other routes are accepted. *)

(* Legal, but the mismatch is reported; silence it here. *)
Set Warnings "-notation-incompatible-level".

(* Against a reserved (hence parsing) notation. *)
Module WithReservedNotation.
  Reserved Notation "x =? y" (at level 70, no associativity).
  Declare Scope test_expr_scope.
  Notation "a1 =? a2" := (andb a1 a2)
    (only printing, a2 at level 16, left associativity, at level 17) : test_expr_scope.
  Notation "x =? y" := (Nat.eqb x y) : nat_scope.
  Check (0 =? 1).
End WithReservedNotation.

(* Same, with a reserved "only printing" notation. *)
Module WithReservedOnlyPrintingNotation.
  Reserved Notation "x <?> y" (at level 70, no associativity).
  Reserved Notation "x <?> y" (only printing, at level 17, left associativity, y at level 16).
  Notation "x <?> y" := (Nat.eqb x y) : nat_scope.
  Check (0 <?> 1).
End WithReservedOnlyPrintingNotation.

(* The reverse order is accepted too.  There the later declaration brings the
   parsing rule, and the level recorded by the earlier one stays. *)
Module ParsingAfterOnlyPrinting.
  Declare Scope test_a_scope.
  Notation "x <+> y" := (andb x y)
    (only printing, at level 17, left associativity, y at level 16) : test_a_scope.
  Declare Scope test_b_scope.
  Notation "x <+> y" := (Nat.eqb x y) (at level 70, no associativity) : test_b_scope.
  Open Scope test_b_scope.
  Check (0 <+> 1).
End ParsingAfterOnlyPrinting.
