Module Postponing.

Class In A T := { IsIn : A -> T -> Prop }.
Class Empty T := { empty : T }.
Class EmptyIn (A T : Type) `{In A T} `{Empty T} :=
 { isempty : forall x, IsIn x empty -> False }.

#[export] Hint Mode EmptyIn ! ! - - : typeclass_instances.
#[export] Hint Mode Empty ! : typeclass_instances.
#[export] Hint Mode In ! - : typeclass_instances.
Existing Class IsIn.
Goal forall A T `{In A T} `{Empty T} `{EmptyIn A T}, forall x : A, IsIn x empty -> False.
 Proof.
   intros.
   eapply @isempty. (* Second goal needs to be solved first, to un-stuck the first one
   (hence the Existing Class IsIn to allow finding the assumption of IsIn here)  *)
   all:typeclasses eauto.
Qed.

End Postponing.

Module Heads.
  Set Primitive Projections.
  Class A (X : Type) := { somex : X }.
  Local Hint Mode A ! : typeclass_instances.

  Record foo := { car : Type; obj : car }.
  Local Instance foo_A (f : foo) : A (car f) := { somex := obj f }.

  Definition onef := {| car := nat; obj := 0 |}.
  Goal  {f : foo & A (car f)}.
  Proof.
    unshelve eexists; cycle 1.
    solve [typeclasses eauto].
    exact onef.
  Defined.
End Heads.

Module BestEffort.

  Class A (T : Type).
  Global Hint Mode A + : typeclass_instances.
  Class B (T : Type).
  Global Hint Mode B + : typeclass_instances.

  #[export] Instance a_imp_b T : A T -> B T := {}.
  #[export] Instance anat : B nat := {}.
  Lemma b : B nat * A nat.
  Proof.
    Fail split; typeclasses eauto.
    Set Typeclasses Debug Verbosity 2.
    Fail split; solve [typeclasses eauto best_effort].
    (* Here typeclasses eauto best_effort, when run on the 2 goals at once,
       can solve the B goal which has a nat instance nd whose mode is +
       (this morally assumes that there is only one instance matching B nat)
    *)
    split; typeclasses eauto best_effort.
    admit.
  Admitted.

End BestEffort.

Module Plus.
  Parameter plus : nat -> nat -> nat -> Prop.

  Axiom plus0l : forall m : nat, plus 0 m m.
  Axiom plus0r : forall n : nat, plus n 0 n.
  Axiom plusSl : forall n m r : nat, plus n m r -> plus (S n) m (S r).
  Axiom plusSr : forall n m r : nat, plus n m r -> plus m (S m) (S r).

  Hint Resolve plus0l plus0r plusSl plusSr : plus.
  Hint Mode plus ! - - : plus.
  Hint Mode plus - ! - : plus.

  Require Corelib.derive.Derive.
  Derive r SuchThat (plus 1 4 r) As r_proof.
  Proof.
    subst r. typeclasses eauto with plus.
  Qed.

  Goal exists x y, plus x y 12.
  Proof.
    eexists ?[x], ?[y].
    Set Typeclasses Debug.
    Fail typeclasses eauto with plus.
    instantiate (y := 1).
    typeclasses eauto with plus.
  Defined.
End Plus.

Module Frozen.
  Record bi := {
      car :> Type;
      emp : car;
      foo : car;
      of_bool : bool -> car;
      to_prop : car -> Prop;
      to_prop_true : to_prop (of_bool true);
    }.
  Arguments emp {_}.
  Arguments foo {_}.
  Arguments of_bool {_}.
  Arguments to_prop {_}.

  Class Special {PROP:bi} (P : PROP) : Prop := {}.

  Instance emp_Special {PROP:bi} : Special PROP.(emp) | 1 := {}.
  Instance of_bool_false_Special {PROP:bi} : Special (PROP.(of_bool) false) | 1 := {}.
 (* [True] is a placeholder for some condition that is not part of the TC
  hierarchy, which is why [of_bool_true_Special] is not an instance. *)
  Definition of_bool_true_Special {PROP:bi} : True -> Special (PROP.(of_bool) true) := fun _ => Build_Special _ _.


  Inductive is_of_bool_false {PROP:bi} : forall (P:PROP), Prop :=
  | Exactly : is_of_bool_false (of_bool false).

  (* [some_bi] is interesting because it has [to_prop (of_bool false)] *)
  Axiom some_bi : bi.
  Axiom some_bi_to_prop_false : some_bi.(to_prop) (of_bool false).

  (* [special_bi] is interesting because all its members are [Special] *)
  Axiom special_bi : bi.
  Instance special_bi_Special : forall P: special_bi, Special P | 0 := {}.

  Section ModeOO.
    Hint Mode Special - - : typeclass_instances.

    Goal exists PROP, Special (PROP.(emp)).
    Proof.
      eexists ?[PROP].
      apply _.                    (* not desireable because it picked a fixed bi *)
      Fail [PROP]: exact some_bi.
    Abort.

    Goal forall {PROP:bi}, exists P : PROP,
        Special P /\ to_prop P.
    Proof.
      intros. eexists ?[P].
      split.
      - apply _.  (* not desired because it picks a value for [P] arbitrarily *)
      -           (* stuck because we should have picked [of_bool true] *)
    Abort.

    Goal forall {PROP:bi}, exists b:bool,
        Special (PROP.(of_bool) b) /\ PROP.(to_prop) (of_bool b).
    Proof.
      intros. eexists ?[P].
      split.
      - apply _.  (* not desired because it picks a value for [b] arbitrarily *)
      - Fail apply to_prop_true. (* stuck because we should have picked [true] *)
    Abort.

    Goal exists PROP:bi, exists P:PROP, Special P /\ is_of_bool_false P /\ to_prop P.
    Proof.
      eexists ?[PROP], ?[P].
      split; [|split].
      - apply _.             (* not desired because it picked an arbitrary value for [PROP] *)
      - constructor.
      - Fail apply some_bi_to_prop_false. (* stuck *)
    Abort.

    Goal exists PROP:bi, exists b:bool,
        Special (PROP.(of_bool) b) /\ PROP.(to_prop) (of_bool b) /\ not (is_true b).
    Proof.
      eexists ?[PROP], ?[b].
      split; [|split].
      - apply _.             (* not desired because it picked arbitrary values for [PROP] and [b] *)
      - apply to_prop_true.  (* stuck because we should have picked [true] *)
    Abort.

    Goal exists PROP:bi, Special (PROP.(of_bool) false) /\ PROP.(to_prop) (of_bool false).
    Proof.
      eexists ?[PROP].
      split.
      - apply _.                (* picked the wrong bi *)
      -                         (* stuck *)
    Abort.
  End ModeOO.

  Section ModeOI.
    Hint Mode Special - + : typeclass_instances.

    Goal exists PROP, Special (PROP.(emp)).
    Proof.
      eexists.
      Fail apply _.             (* would be fine but does not work with [+] *)
    Abort.

    Goal forall {PROP:bi}, exists P : PROP,
        Special P /\ to_prop P.
    Proof.
      intros. eexists.
      split.
      - Fail apply _.                  (* Correctly fails *)
        apply of_bool_true_Special. constructor.
      - apply to_prop_true.
    Qed.

    Goal forall {PROP:bi}, exists b:bool,
        Special (PROP.(of_bool) b) /\ PROP.(to_prop) (of_bool b).
    Proof.
      intros. eexists.
      split.
      - Fail apply _.           (* Correctly fails. *)
        apply of_bool_true_Special. constructor.
      - apply to_prop_true.
    Qed.

    Goal exists PROP:bi, exists P:PROP, Special P /\ is_of_bool_false P /\ to_prop P.
    Proof.
      eexists ?[PROP], ?[P].
      split; [|split].
      - Fail apply _.           (* fails correctly *)
        apply (@of_bool_false_Special some_bi).
      - constructor.
      - apply some_bi_to_prop_false.
    Qed.

    Goal exists PROP:bi, exists b:bool,
        Special (PROP.(of_bool) b) /\ PROP.(to_prop) (of_bool b).
    Proof.
      eexists ?[PROP], ?[P].
      split.
      - Fail apply _.           (* fails correctly *)
        apply (@of_bool_true_Special some_bi). constructor.
      - apply to_prop_true.
    Qed.

    Goal exists PROP:bi, exists b:bool,
        Special (PROP.(of_bool) b) /\ PROP.(to_prop) (of_bool b) /\ not (is_true b).
    Proof.
      eexists ?[PROP], ?[b].
      split; [|split].
      - Fail apply _.           (* fails correctly *)
        apply (@of_bool_false_Special some_bi).
      - apply some_bi_to_prop_false.
      - intro H. discriminate H.
    Qed.

    Goal exists PROP:bi, Special (PROP.(of_bool) false) /\ PROP.(to_prop) (of_bool false).
    Proof.
      eexists ?[PROP].
      split.
      - Fail apply _.           (* fails but could be OK *)
    Abort.
  End ModeOI.

  Section ModeOH.
    Hint Mode Special - ! : typeclass_instances.

    Goal exists PROP, Special (PROP.(emp)).
    Proof.
      eexists.
      apply _.                    (* not desireable because it picked a fixed bi *)
      Fail [PROP]: exact some_bi.
    Abort.

    Goal forall {PROP:bi}, exists P : PROP,
        Special P /\ to_prop P.
    Proof.
      intros. eexists ?[P].
      split.
      - Fail apply _.      (* Correctly fails but only because [P] is exactly an evar *)
        apply of_bool_true_Special. constructor.
      - apply to_prop_true.
    Qed.

    Goal forall {PROP:bi}, exists b:bool,
        Special (PROP.(of_bool) b) /\ PROP.(to_prop) (of_bool b).
    Proof.
      intros. eexists.
      split.
      - apply _.  (* undesirable because it picks a value for [b] arbitrarily *)
      - Fail apply to_prop_true. (* stuck because we should have picked [true] *)
    Abort.

    Goal exists PROP:bi, exists P:PROP, Special P /\ is_of_bool_false P /\ to_prop P.
    Proof.
      eexists ?[PROP], ?[P].
      split; [|split].
      - Fail apply _.           (* fails correctly but only because [P] is exactly an evar *)
        apply (@of_bool_false_Special some_bi).
      - constructor.
      - apply some_bi_to_prop_false.
    Qed.

    Goal exists PROP:bi, exists b:bool,
        Special (PROP.(of_bool) b) /\ PROP.(to_prop) (of_bool b) /\ not (is_true b).
    Proof.
      eexists ?[PROP], ?[b].
      split; [|split].
      - apply _.                (* not desired because it picked arbitrary values for [PROP] and [b] *)
      - apply to_prop_true.     (* stuck because we should have picked [true] *)
    Abort.

    Goal exists PROP:bi, Special (PROP.(of_bool) false) /\ PROP.(to_prop) (of_bool false).
    Proof.
      eexists ?[PROP].
      split.
      - apply _.                (* picked the wrong bi *)
      -                         (* stuck *)
    Abort.
  End ModeOH.

  Section ModeOF.
    Hint Mode Special - = : typeclass_instances.

    Goal exists PROP, Special (PROP.(emp)).
    Proof.
      eexists ?[PROP].
      apply _.                    (* works and does not pick a bi *)
      [PROP]: exact some_bi.
    Qed.

    Goal forall {PROP:bi}, exists P : PROP,
        Special P /\ to_prop P.
    Proof.
      intros. eexists ?[P].
      split.
      - Fail apply _.      (* Correctly fails but only because [P] is exactly an evar *)
        apply of_bool_true_Special. constructor.
      - apply to_prop_true.
    Qed.

    Goal forall {PROP:bi}, exists b:bool,
        Special (PROP.(of_bool) b) /\ PROP.(to_prop) (of_bool b).
    Proof.
      intros. eexists.
      split.
      - Fail apply _.           (* fails correctly *)
        apply of_bool_true_Special. constructor.
      - apply to_prop_true.
    Qed.

    Goal exists PROP:bi, exists P:PROP, Special P /\ is_of_bool_false P /\ to_prop P.
    Proof.
      eexists ?[PROP], ?[P].
      split; [|split].
      - apply _.                (* undesired it because it picked [PROP:=special_bi] *)
      - constructor.
      - Fail apply some_bi_to_prop_false. (* stuck *)
    Abort.

    Goal exists PROP:bi, exists b:bool,
        Special (PROP.(of_bool) b) /\ PROP.(to_prop) (of_bool b) /\ not (is_true b).
    Proof.
      eexists ?[PROP], ?[P].
      split; [|split].
      - Fail apply _.        (* fails correctly even when [?b] is deeper in the term. *)
        apply (@of_bool_false_Special some_bi).
      - apply some_bi_to_prop_false.
      - intro H. discriminate H.
    Qed.

    Goal exists PROP:bi, Special (PROP.(of_bool) false) /\ PROP.(to_prop) (of_bool false).
    Proof.
      eexists ?[PROP].
      split.
      - apply _.                (* works and does not pick a bi *)
      - apply some_bi_to_prop_false.
    Qed.
  End ModeOF.


  Section ModeFF.
    Hint Mode Special = = : typeclass_instances.

    Goal exists PROP, Special (PROP.(emp)).
    Proof.
      eexists ?[PROP].
      apply _.                    (* works and does not pick a bi *)
      [PROP]: exact some_bi.
    Qed.

    Goal forall {PROP:bi}, exists P : PROP,
        Special P /\ to_prop P.
    Proof.
      intros. eexists ?[P].
      split.
      - Fail apply _.      (* Correctly fails but only because [P] is exactly an evar *)
        apply of_bool_true_Special. constructor.
      - apply to_prop_true.
    Qed.

    Goal forall {PROP:bi}, exists b:bool,
        Special (PROP.(of_bool) b) /\ PROP.(to_prop) (of_bool b).
    Proof.
      intros. eexists.
      split.
      - Fail apply _.           (* fails correctly *)
        apply of_bool_true_Special. constructor.
      - apply to_prop_true.
    Qed.

    (* This case is the only difference between [ModeOF] and [ModeFF] *)
    Goal exists PROP:bi, exists P:PROP, Special P /\ is_of_bool_false P /\ to_prop P.
    Proof.
      eexists ?[PROP], ?[P].
      split; [|split].
      - Fail apply _.                (* correctly fails to apply *)
        apply of_bool_false_Special.
      - constructor.
      - apply some_bi_to_prop_false.
    Qed.

    Goal exists PROP:bi, exists b:bool,
        Special (PROP.(of_bool) b) /\ PROP.(to_prop) (of_bool b) /\ not (is_true b).
    Proof.
      eexists ?[PROP], ?[b].
      split; [|split].
      - Fail apply _.        (* fails correctly even when [?b] is deeper in the term. *)
        apply (@of_bool_false_Special some_bi).
      - apply some_bi_to_prop_false.
      - intro H. discriminate H.
    Qed.

    Goal exists PROP:bi, Special (PROP.(of_bool) false) /\ PROP.(to_prop) (of_bool false).
    Proof.
      eexists ?[PROP].
      split.
      - apply _.                (* works and does not pick a bi *)
      - apply some_bi_to_prop_false.
    Qed.
  End ModeFF.
End Frozen.

Module ModeAttr.
  Fail #[mode="+"] Inductive foo (A : Type) : Set :=.

  Fail #[mode=""] Class Foo (A : Type) := {}.
  Succeed #[mode="+"] Class Foo (A : Type) := {}.
  Succeed #[mode="="] Class Foo (A : Type) := {}.
  Fail #[mode="+ +"] Class Foo' (A : Type) := {}.
End ModeAttr.
