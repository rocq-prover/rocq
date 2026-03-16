Require Import Ltac2.Ltac2.

Definition myid {A} (x : A) := x.

Ltac2 myid_ref () :=
  match Env.expand [@myid] with
  | r :: _ => r
  | [] => Control.throw (Invalid_argument (Some (Message.of_string "myid not found")))
  end.

Ltac2 unfold_myid () :=
  Std.unfold [(myid_ref (), Std.AllOccurrences)]
    {Std.on_hyps := None; Std.on_concl := Std.AllOccurrences}.

(* Test with_strategy Expand allows unfolding an opaque constant *)
Opaque myid.
Goal myid 0 = 0.
  TransparentState.with_strategy TransparentState.Expand [myid_ref ()]
    (fun () => unfold_myid ()).
  reflexivity.
Qed.

(* Test that strategy is restored after the tactic *)
Goal myid 0 = 0.
  TransparentState.with_strategy TransparentState.Expand [myid_ref ()]
    (fun () => ()).
  (* unfold should fail since myid is opaque again *)
  Fail unfold myid.
  reflexivity.
Qed.

(* Test with Level 0 = transparent *)
Goal myid 0 = 0.
  TransparentState.with_strategy (TransparentState.Level 0) [myid_ref ()]
    (fun () => unfold_myid ()).
  reflexivity.
Qed.

(* Test Opaque: making a transparent constant temporarily opaque *)
Transparent myid.
Goal myid 0 = 0.
  TransparentState.with_strategy TransparentState.Opaque [myid_ref ()]
    (fun () => ()).
  (* myid should be transparent again after with_strategy *)
  unfold_myid ().
  reflexivity.
Qed.
