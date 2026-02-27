From Corelib Require Import BinNums RatDef micromega_formula micromega_witness.
From Corelib Require Import micromega_tactics.

Goal True.
Proof.
(* x + 2 y <= 3 -> 2 x + y <= 3 -> x + y <= 2 *)
pose (ffQ :=
  IMPL
    (EQ
       (A isBool
          {|
            Flhs := PEadd (PEX _ xH) (PEmul (PEc (Qmake (Zpos (xO xH)) xH)) (PEX _ (xO xH)));
            Fop := OpLe;
            Frhs := PEc (Qmake (Zpos (xI xH)) xH)
          |} tt) (TT isBool)) None
    (IMPL
       (EQ
          (A isBool
             {|
               Flhs := PEadd (PEmul (PEc (Qmake (Zpos (xO xH)) xH)) (PEX _ xH)) (PEX _ (xO xH));
               Fop := OpLe;
               Frhs := PEc (Qmake (Zpos (xI xH)) xH)
             |} tt) (TT isBool)) None
       (EQ
          (A isBool
             {| Flhs := PEadd (PEX _ xH) (PEX _ (xO xH)); Fop := OpLe; Frhs := PEc (Qmake (Zpos (xO xH)) xH) |} tt)
          (TT isBool))) : BFormula (Formula Q) isProp).
let ff' := eval unfold ffQ in ffQ in wlra_Q wit0 ff'.
Check eq_refl : wit0 = (PsatzAdd (PsatzIn Q 2)
  (PsatzAdd (PsatzIn Q 1) (PsatzMulE (PsatzC (Qmake (Zpos (xI xH)) xH)) (PsatzIn Q 0))) :: nil)%list.
(* indeed, ff is normalized to:
   ~ (x + y - 2 > 0 /\ - 2 x - y + 3 >= 0 /\ - x - 2 y + 3 >= 0)
      \-----v-----/    \-------v--------/    \-------v--------/
           (0)                (1)                   (2)
   witness is (2) + (1) + 3 * (0) meaning that (0) /\ (1) /\ (2) implies 0 > 0
   which is inconsistent and proves the original formula by contraposite. *)
(* 2 * x <= 1 -> x <= 0 *)
pose (ffZ :=
  IMPL
    (A isProp
       {|
         Flhs := PEmul (PEc (Zpos (xO xH))) (PEX _ xH);
         Fop := OpLe;
         Frhs := PEc (Zpos xH)
       |} tt) None
    (A isProp
       {|
         Flhs := PEX _ xH;
         Fop := OpLe;
         Frhs := PEc Z0
       |} tt) : BFormula (Formula Z) isProp).
let ff' := eval unfold ffZ in ffZ in wlia wit1 ff'.
Check eq_refl : wit1 = (CutProof (PsatzIn Z 1)
  (RatProof (PsatzAdd (PsatzIn Z 0) (PsatzIn Z 1)) DoneProof) :: nil)%list.
let ff' := eval unfold ffZ in ffZ in wnia wit2 ff'.
Check eq_refl : wit2 = (CutProof (PsatzIn Z 1)
  (RatProof (PsatzAdd (PsatzIn Z 0) (PsatzIn Z 1)) DoneProof) :: nil)%list.
let ff' := eval unfold ffQ in ffQ in wnra_Q wit3 ff'.
Check eq_refl : wit3 = (PsatzAdd (PsatzIn Q 2)
  (PsatzAdd (PsatzIn Q 1) (PsatzMulE (PsatzC (Qmake (Zpos (xI xH)) xH)) (PsatzIn Q 0))) :: nil)%list.
Fail let ff' := eval unfold ffQ in ffQ in wsos_Q wit4 ff'.
Fail let ff' := eval unfold ffZ in ffZ in wsos_Z wit5 ff'.
(* Requires Csdp, not in CI
let ff' := eval unfold ffZ in ffZ in wpsatz_Z 3 wit6 ff'.
Check eq_refl : wit6 = (RatProof (PsatzAdd (PsatzC (Zpos xH))
  (PsatzAdd (PsatzIn Z 1) (PsatzMulE (PsatzC (Zpos (xO xH))) (PsatzIn Z 0))))
  DoneProof :: nil)%list.
let ff' := eval unfold ffQ in ffQ in wpsatz_Q 3 wit7 ff'.
Check eq_refl : wit7 = (PsatzAdd (PsatzIn Q 0)
  (PsatzAdd (PsatzMulE (PsatzIn Q 2) (PsatzC (Qmake (Zpos xH) (xO xH))))
            (PsatzAdd (PsatzMulE (PsatzIn Q 1) (PsatzC (Qmake (Zpos xH) (xO xH))))
                      (PsatzMulE (PsatzIn Q 0) (PsatzC (Qmake (Zpos xH) (xO xH)))))) :: nil)%list. *)
(* (0) + 1/2 * (2) + 1/2 * (1) + 1/2 * (0) *)
Abort.
