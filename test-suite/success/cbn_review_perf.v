(* Performance regressions surfaced by the delayed-substitution [cbn] review. *)

From Corelib Require Import PrimInt63 PrimArray.

Open Scope uint63_scope.
Open Scope array_scope.

Ltac mk_nat n :=
  lazymatch n with
  | O => constr:(O)
  | S ?n' => let t := mk_nat n' in constr:(S t)
  end.

Ltac setup_nat_goal t := enough (t = O) by exact I.

(* 1. Refolding should not force the stuck eliminator it is about to
      replace by the original constant.  These counts are from master
      before delayed substitutions. *)
Definition stuck_case_review (branch x : nat) : nat :=
  (fun y : nat => match x with O => y | S _ => y end) branch.

Goal True.
Proof.
  let branch := mk_nat 50%nat in
  enough (forall x : nat, stuck_case_review branch x = stuck_case_review branch x) by exact I.
  (* master: 381,487 instructions *)
  Instructions cbn.
Abort.

Goal True.
Proof.
  let branch := mk_nat 100%nat in
  enough (forall x : nat, stuck_case_review branch x = stuck_case_review branch x) by exact I.
  (* master: 678,771 instructions *)
  Instructions cbn.
Abort.

Goal True.
Proof.
  let branch := mk_nat 200%nat in
  enough (forall x : nat, stuck_case_review branch x = stuck_case_review branch x) by exact I.
  (* master: 1,266,039 instructions *)
  Instructions cbn.
Abort.

Goal True.
Proof.
  let branch := mk_nat 50%nat in
  enough (((fun y : nat =>
              (fix stuck_fix_review (n : nat) : nat :=
                 match n with O => y | S n' => stuck_fix_review n' end)) branch)
          = ((fun y : nat =>
                (fix stuck_fix_review (n : nat) : nat :=
                   match n with O => y | S n' => stuck_fix_review n' end)) branch)) by exact I.
  (* master: 371,665 instructions *)
  Instructions cbn.
Abort.

Goal True.
Proof.
  let branch := mk_nat 100%nat in
  enough (((fun y : nat =>
              (fix stuck_fix_review (n : nat) : nat :=
                 match n with O => y | S n' => stuck_fix_review n' end)) branch)
          = ((fun y : nat =>
                (fix stuck_fix_review (n : nat) : nat :=
                   match n with O => y | S n' => stuck_fix_review n' end)) branch)) by exact I.
  (* master: 648,158 instructions *)
  Instructions cbn.
Abort.

(* 2. Primitive [array_get] at index zero should not force every delayed
      element of the array literal.  The master counts below come from the
      review reproducer. *)
Definition delayed_nat_array_16 (x : nat) : array nat :=
  [| x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x | x |].

Definition delayed_nat_array_32 (x : nat) : array nat :=
  [| x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x | x |].

Definition delayed_nat_array_64 (x : nat) : array nat :=
  [| x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x | x |].

Definition delayed_nat_array_128 (x : nat) : array nat :=
  [| x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x | x |].

Definition delayed_nat_array_256 (x : nat) : array nat :=
  [| x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x; x | x |].

Goal True.
Proof.
  enough (((fun x : nat => (delayed_nat_array_16 x).[0]) O) = O) by exact I.
  (* master: 69,367 instructions *)
  Instructions cbn.
Abort.

Goal True.
Proof.
  enough (((fun x : nat => (delayed_nat_array_32 x).[0]) O) = O) by exact I.
  (* master: 70,998 instructions *)
  Instructions cbn.
Abort.

Goal True.
Proof.
  enough (((fun x : nat => (delayed_nat_array_64 x).[0]) O) = O) by exact I.
  (* master: 76,393 instructions *)
  Instructions cbn.
Abort.

Goal True.
Proof.
  enough (((fun x : nat => (delayed_nat_array_128 x).[0]) O) = O) by exact I.
  (* master: 80,704 instructions *)
  Instructions cbn.
Abort.

Goal True.
Proof.
  enough (((fun x : nat => (delayed_nat_array_256 x).[0]) O) = O) by exact I.
  (* master: 95,757 instructions *)
  Instructions cbn.
Abort.

(* 3. Progress/equality checks for [simpl nomatch] must not force an
      unused large parameter.  These master counts intentionally show the
      old linear dependence on [big]; delayed closures should do better
      and future changes should not reintroduce the branch regression. *)
Fixpoint nomatch_progress_review (fuel : nat) (big : nat) (b : bool) : bool :=
  match fuel with
  | O => if b then true else false
  | S fuel' => nomatch_progress_review fuel' big b
  end.
Arguments nomatch_progress_review : simpl nomatch.

Goal True.
Proof.
  let big := mk_nat 100%nat in
  enough (forall b : bool, nomatch_progress_review 30%nat big b = b) by exact I.
  (* master: 19,228,149 instructions *)
  Instructions cbn.
Abort.

Goal True.
Proof.
  let big := mk_nat 500%nat in
  enough (forall b : bool, nomatch_progress_review 30%nat big b = b) by exact I.
  (* master: 81,531,782 instructions *)
  Instructions cbn.
Abort.

Goal True.
Proof.
  let big := mk_nat 1000%nat in
  enough (forall b : bool, nomatch_progress_review 30%nat big b = b) by exact I.
  (* master: 159,320,447 instructions *)
  Instructions cbn.
Abort.
