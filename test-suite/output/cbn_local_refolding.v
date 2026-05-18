(* Regression tests for cbn refolding with local definitions.
   The expected output is the behavior of master: [simpl nomatch]
   wrappers must remain folded when unfolding them would expose a stuck
   match/let-pattern in head position, even when the wrapper, dictionary, or
   arguments pass through local definitions. *)

Set Printing Width 200.
Require Import PrimString.
Open Scope pstring_scope.

Module IdentityLocalLets.
  Definition id (n : nat) := n.
  Definition fstn (x y : nat) := x.
  Definition sndn (x y : nat) := y.
  Definition pcase (n : nat) := match n with O => O | S p => p end.
  Arguments id n / : simpl nomatch.
  Arguments fstn x y / : simpl nomatch.
  Arguments sndn x y / : simpl nomatch.

  Check "id: let match arg".
  Eval cbn in (fun x : nat => id (let y := match x with O => O | S p => p end in y)).

  Check "id: let pcase arg".
  Eval cbn in (fun x : nat => id (let y := pcase x in y)).

  Check "id: let-bound function".
  Eval cbn in (fun x : nat => let local_pcase := fun n : nat => match n with O => O | S p => p end in id (local_pcase x)).

  Check "fst: let match arg".
  Eval cbn in (fun x : nat => fstn (let y := match x with O => O | S p => p end in y) O).

  Check "snd: let match arg".
  Eval cbn in (fun x : nat => sndn O (let y := match x with O => O | S p => p end in y)).

  Goal forall x : nat, True.
  Proof.
    intro x.
    pose (local_pcase := fun n : nat => match n with O => O | S p => p end).
    Check "id: proof local function".
    Eval cbn in (id (local_pcase x)).
    exact I.
  Qed.
End IdentityLocalLets.

Module SectionLetLocalDefinition.
  Definition id (n : nat) := n.
  Arguments id n / : simpl nomatch.

  Section S.
    Let sec_pcase (n : nat) := match n with O => O | S p => p end.

    Check "id: section let function".
    Eval cbn in (fun x : nat => id (sec_pcase x)).
  End S.
End SectionLetLocalDefinition.

Module DefClassLocalLets.
  Definition Difference A := A -> A -> A.
  Definition difference {A} {D : Difference A} : A -> A -> A := D.
  Definition dnat : Difference nat := fun x y => match x with O => y | S z => z end.
  Arguments difference {A} D / _ _ : simpl nomatch.

  Check "def: let dictionary".
  Eval cbn in (fun x : nat => let D := dnat in @difference nat D x (S O)).

  Check "def: let open arg".
  Eval cbn in (fun x : nat => let x' := x in @difference nat dnat x' (S O)).

  Check "def: let beta open arg".
  Eval cbn in (fun x : nat => let x' := (fun z : nat => z) x in @difference nat dnat x' (S O)).

  Check "def: nested let dictionary and arg".
  Eval cbn in (fun x : nat => let D := dnat in let x' := x in @difference nat D x' (S O)).

  Check "def: let wrapper".
  Eval cbn in (fun x : nat => let f := @difference nat dnat in f x (S O)).

  Check "def: let in dictionary body".
  Eval cbn in (fun x : nat => @difference nat (let D := dnat in D) x (S O)).

  Check "def: closed constructor control".
  Eval cbn in (fun y : nat => let x' := O in @difference nat dnat x' y).
End DefClassLocalLets.

Module ClassLocalLets.
  Class Difference A := difference : A -> A -> A.
  Definition dnat : Difference nat := fun x y => match x with O => y | S z => z end.
  Arguments difference {A} Difference / _ _ : simpl nomatch.

  Check "class: let dictionary".
  Eval cbn in (fun x : nat => let D := dnat in @difference nat D x (S O)).

  Check "class: let open arg".
  Eval cbn in (fun x : nat => let x' := x in @difference nat dnat x' (S O)).

  Check "class: let beta open arg".
  Eval cbn in (fun x : nat => let x' := (fun z : nat => z) x in @difference nat dnat x' (S O)).

  Check "class: nested let dictionary and arg".
  Eval cbn in (fun x : nat => let D := dnat in let x' := x in @difference nat D x' (S O)).

  Check "class: let wrapper".
  Eval cbn in (fun x : nat => let f := @difference nat dnat in f x (S O)).

  Check "class: let in dictionary body".
  Eval cbn in (fun x : nat => @difference nat (let D := dnat in D) x (S O)).

  Check "class: closed constructor control".
  Eval cbn in (fun y : nat => let x' := O in @difference nat dnat x' y).
End ClassLocalLets.

Module SetLocalLets.
  Definition Difference A := A -> A -> A.
  Definition difference {A} {D : Difference A} : A -> A -> A := D.
  Definition set := { t : nat | True }.
  Definition set0 : set := exist _ O I.
  Definition setS (n : nat) : set := exist _ (S n) I.
  Definition set_difference : Difference set := fun X Y => let (t1, _) := X in let (t2, _) := Y in exist _ t1 I.
  Arguments difference {A} D / _ _ : simpl nomatch.

  Check "set: let dictionary".
  Eval cbn in (fun y : set => let D := set_difference in @difference set D set0 y).

  Check "set: let open second arg".
  Eval cbn in (fun y : set => let y' := y in @difference set set_difference set0 y').

  Check "set: let wrapper".
  Eval cbn in (fun y : set => let f := @difference set set_difference in f set0 y).

  Check "set: closed constructor control".
  Eval cbn in (let D := set_difference in @difference set D set0 (setS O)).
End SetLocalLets.

Module DictionaryBodiesWithLets.
  Definition Difference A := A -> A -> A.
  Definition difference {A} {D : Difference A} : A -> A -> A := D.
  Arguments difference {A} D / _ _ : simpl nomatch.

  Definition dlet_arg : Difference nat := fun x y => let z := x in match z with O => y | S w => w end.
  Definition dlet_branch : Difference nat := fun x y => match x with O => let z := y in z | S w => w end.
  Definition dlet_fun : Difference nat := let D := fun x y => match x with O => y | S w => w end in D.

  Check "body: let around scrutinee".
  Eval cbn in (fun x : nat => @difference nat dlet_arg x (S O)).

  Check "body: let in branch".
  Eval cbn in (fun x : nat => @difference nat dlet_branch x (S O)).

  Check "body: dictionary constant is let".
  Eval cbn in (fun x : nat => @difference nat dlet_fun x (S O)).

  Check "body: closed constructor control".
  Eval cbn in (fun y : nat => @difference nat dlet_arg O y).
End DictionaryBodiesWithLets.

Module ProofLocalDefinitions.
  Definition Difference A := A -> A -> A.
  Definition difference {A} {D : Difference A} : A -> A -> A := D.
  Definition dnat : Difference nat := fun x y => match x with O => y | S z => z end.
  Arguments difference {A} D / _ _ : simpl nomatch.

  Goal forall x : nat, True.
  Proof.
    intro x.
    pose (D := dnat).
    Check "proof local: dictionary".
    Eval cbn in (@difference nat D x (S O)).
    exact I.
  Qed.

  Goal forall x : nat, True.
  Proof.
    intro x.
    pose (x' := x).
    Check "proof local: open arg".
    Eval cbn in (@difference nat dnat x' (S O)).
    exact I.
  Qed.

  Goal forall x : nat, True.
  Proof.
    intro x.
    pose (f := @difference nat dnat).
    Check "proof local: wrapper".
    Eval cbn in (f x (S O)).
    exact I.
  Qed.

  Goal forall x : nat, True.
  Proof.
    intro x.
    pose (D := fun a b : nat => match a with O => b | S z => z end).
    Check "proof local: inline dictionary".
    Eval cbn in (@difference nat D x (S O)).
    exact I.
  Qed.
End ProofLocalDefinitions.

Module ProofLocalSetDefinitions.
  Definition Difference A := A -> A -> A.
  Definition difference {A} {D : Difference A} : A -> A -> A := D.
  Definition set := { t : nat | True }.
  Definition set0 : set := exist _ O I.
  Definition set_difference : Difference set := fun X Y => let (t1, _) := X in let (t2, _) := Y in exist _ t1 I.
  Arguments difference {A} D / _ _ : simpl nomatch.

  Goal forall y : set, True.
  Proof.
    intro y.
    pose (D := set_difference).
    Check "proof local set: dictionary".
    Eval cbn in (@difference set D set0 y).
    exact I.
  Qed.

  Goal forall y : set, True.
  Proof.
    intro y.
    pose (y' := y).
    Check "proof local set: open arg".
    Eval cbn in (@difference set set_difference set0 y').
    exact I.
  Qed.

  Goal forall y : set, True.
  Proof.
    intro y.
    pose (f := @difference set set_difference).
    Check "proof local set: wrapper".
    Eval cbn in (f set0 y).
    exact I.
  Qed.
End ProofLocalSetDefinitions.

Module CbnTacticGoals.
  Definition Difference A := A -> A -> A.
  Definition difference {A} {D : Difference A} : A -> A -> A := D.
  Definition dnat : Difference nat := fun x y => match x with O => y | S z => z end.
  Arguments difference {A} D / _ _ : simpl nomatch.

  Goal forall x : nat, True.
  Proof.
    intro x.
    pose (D := dnat).
    enough (@difference nat D x (S O) = @difference nat D x (S O)) by exact I.
    Check "tactic: proof local dictionary".
    cbn.
    Show.
  Abort.

  Goal forall x : nat, True.
  Proof.
    intro x.
    enough ((let D := dnat in @difference nat D x (S O)) = (let D := dnat in @difference nat D x (S O))) by exact I.
    Check "tactic: term let dictionary".
    cbn.
    Show.
  Abort.

  Goal forall x : nat, True.
  Proof.
    intro x.
    pose (x' := x).
    enough (@difference nat dnat x' (S O) = @difference nat dnat x' (S O)) by exact I.
    Check "tactic: proof local arg".
    cbn.
    Show.
  Abort.
End CbnTacticGoals.
