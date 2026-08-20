Unset Elimination Schemes.
Module Test1.
  Module Type S.
    Inductive T := c (x : nat) (z : nat := 0).
  End S.
  Module A.
    Inductive T := c (z : nat := 0) (x : nat).
  End A.
  Module F (X : S).
    Definition result :
      match (match X.c 1 with X.c x z => z end) with
      | O => True | S _ => False end := I.
  End F.
  Module Type R. Parameter result : False. End R.

  Fail Module Applied : R := F A.

  (* Definition contradiction : False := Applied.result. *)
  (* Print Assumptions contradiction. *)

  Module B.
    Inductive T := c (z : nat := 0) (k := 0) (x : nat).
  End B.

  (* check that we do a proper error, not anomaly on mismatch decl lengths *)
  Fail Module Applied : R := F B.
End Test1.

Module Test2.
  Module Type M. Inductive I (n := 0) := C (m:=n). End M.

  Module F (X:M).
    Definition getm x := match x with X.C _ m => m end.
    Definition getm_spec : getm X.C = 0 := eq_refl.
  End F.

  Module MI. Inductive I (n:=1) := C (m:=n). End MI.

  Fail Module A := F MI.

  (* Definition getm_spec2 : A.getm MI.C = 1 := eq_refl. *)

  (* Lemma bad : False. *)
  (* Proof. *)
  (*   pose proof A.getm_spec. *)
  (*   pose proof getm_spec2. *)
  (*   discriminate. *)
  (* Qed. *)
End Test2.
