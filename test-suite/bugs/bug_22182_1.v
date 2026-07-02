(* -*- mode: coq; coq-prog-args: ("-noinit") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 2110 lines to 45 lines, then from 59 lines to 571 lines, then from 578 lines to 80 lines, then from 94 lines to 506 lines, then from 513 lines to 101 lines, then from 115 lines to 458 lines, then from 465 lines to 183 lines, then from 197 lines to 579 lines, then from 586 lines to 212 lines, then from 226 lines to 562 lines, then from 569 lines to 266 lines, then from 276 lines to 533 lines, then from 540 lines to 307 lines, then from 318 lines to 396 lines, then from 403 lines to 318 lines, then from 329 lines to 386 lines, then from 393 lines to 335 lines, then from 345 lines to 2457 lines, then from 2433 lines to 344 lines, then from 354 lines to 1160 lines, then from 1165 lines to 373 lines, then from 383 lines to 722 lines, then from 727 lines to 451 lines, then from 461 lines to 500 lines, then from 507 lines to 467 lines, then from 477 lines to 1148 lines, then from 1155 lines to 495 lines, then from 506 lines to 2679 lines, then from 2628 lines to 509 lines, then from 519 lines to 3604 lines, then from 3477 lines to 516 lines, then from 526 lines to 1315 lines, then from 1288 lines to 532 lines, then from 542 lines to 1709 lines, then from 1702 lines to 534 lines, then from 544 lines to 1161 lines, then from 1168 lines to 568 lines, then from 579 lines to 1942 lines, then from 1811 lines to 573 lines, then from 584 lines to 1065 lines, then from 1072 lines to 604 lines, then from 614 lines to 2006 lines, then from 1912 lines to 610 lines, then from 620 lines to 4663 lines, then from 4575 lines to 660 lines, then from 670 lines to 875 lines, then from 881 lines to 721 lines, then from 731 lines to 1004 lines, then from 1011 lines to 728 lines, then from 739 lines to 950 lines, then from 957 lines to 788 lines, then from 795 lines to 788 lines, then from 794 lines to 565 lines, then from 572 lines to 565 lines, then from 0 lines to 565 lines *)
(* coqc version 9.3+alpha compiled with OCaml 4.14.2
   coqtop version 9.3+alpha
   Modules that could not be inlined: Ltac2.Std
   Expected coqc runtime on this file: 0.000 sec
   Expected coqc peak memory usage on this file: 0.0 kb *)
Require Corelib.Init.Notations.
Require Ltac2.Std Ltac2.Unification.

Inductive False : Prop := .
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.


Module Export Init.

Export Corelib.Init.Notations.

Export Corelib.Init.Ltac.

#[global] Unset Universe Checking.

Notation "'∏'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).

Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.

Reserved Notation "X ≃ Y" (at level 80, no associativity).

Reserved Notation "f ~ g" (at level 70, no associativity).

Reserved Notation "p @ q" (at level 60, right associativity).

Reserved Notation "A × B" (at level 75, right associativity).

Reserved Notation "a --> b" (at level 55).

Reserved Notation "X ⨿ Y" (at level 50, left associativity).

Reserved Notation "x ,, y" (at level 60, right associativity).

Ltac simple_rapply p :=
  simple refine p ||
  simple refine (p _) ||
  simple refine (p _ _) ||
  simple refine (p _ _ _) ||
  simple refine (p _ _ _ _) ||
  simple refine (p _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

Tactic Notation "use" uconstr(p) := simple_rapply p.

End Init.
Module Export UniMath.
Module Export Foundations.
Module Export Init.
Include UniMath_DOT_Foundations_DOT_Init_WRAPPED.Init.
End Init.
Module Export Control.

Import Ltac2.Init.

Ltac2 @ external enter : (unit -> unit) -> unit := "rocq-runtime.plugins.ltac2" "enter".

Ltac2 @ external goal : unit -> constr := "rocq-runtime.plugins.ltac2" "goal".

Ltac2 @ external refine : (unit -> constr) -> unit := "rocq-runtime.plugins.ltac2" "refine".
Module Export UniMath_DOT_Foundations_DOT_Preamble_WRAPPED.
Module Export Preamble.

Export UniMath.Foundations.Init.

Definition UU := Type.

Identity Coercion fromUUtoType : UU >-> Sortclass.

Inductive unit : UU :=
    tt : unit.

Inductive coprod (A B:UU) : UU :=
| ii1 : A -> coprod A B
| ii2 : B -> coprod A B.
Arguments ii1 {_ _} _.
Arguments ii2 {_ _} _.

Notation inl := ii1.

Notation inr := ii2.

Notation "X ⨿ Y" := (coprod X Y).

Inductive nat : UU :=
  | O : nat
  | S : nat -> nat.

Declare Scope nat_scope.
Open Scope nat_scope.

Fixpoint add n m :=
  match n with
  | O => m
  | S p => S (p + m)
  end
where "n + m" := (add n m) : nat_scope.

Notation  "0" := (O) : nat_scope.
Notation  "1" := (S 0) : nat_scope.

Inductive paths {A:UU} (a:A) : A -> UU := paths_refl : paths a a.
Notation "a = b" := (paths a b) : type_scope.

Record total2 { T: UU } ( P: T -> UU ) := tpair { pr1 : T; pr2 : P pr1 }.

Arguments tpair {_} _ _ _.
Arguments pr1 {_ _} _.
Arguments pr2 {_ _} _.

Notation "'∑'  x .. y , P" := (total2 (λ x, .. (total2 (λ y, P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.

Notation "x ,, y" := (tpair _ x y).

End Preamble.
Module Export UniMath.
Module Export Foundations.
Module Export Preamble.
Include UniMath_DOT_Foundations_DOT_Preamble_WRAPPED.Preamble.
End Preamble.
Module Export UniMath_DOT_Foundations_DOT_PartA_WRAPPED.
Module Export PartA.

Export UniMath.Foundations.Preamble.

Definition idfun (T : UU) := λ t:T, t.

Definition funcomp {X Y : UU} {Z:Y->UU} (f : X -> Y) (g : ∏ y:Y, Z y) := λ x, g (f x).

Definition dirprod (X Y : UU) := ∑ x:X, Y.

Notation "A × B" := (dirprod A B) : type_scope.
Definition make_dirprod {X Y : UU} (x:X) (y:Y) : X × Y.
Admitted.

Definition pathscomp0 {X : UU} {a b c : X} (e1 : a = b) (e2 : b = c) : a = c.
Admitted.

Notation "p @ q" := (pathscomp0 p q).

Definition maponpaths {T1 T2 : UU} (f : T1 -> T2) {t1 t2 : T1}
           (e: t1 = t2) : f t1 = f t2.
Admitted.

Definition homot {X : UU} {P : X -> UU} (f g : ∏ x : X, P x) := ∏ x : X , f x = g x.

Notation "f ~ g" := (homot f g).
Definition isweq {X Y : UU} (f : X -> Y) : UU.
Admitted.
Definition weq (X Y : UU) : UU.
exact (∑ f:X->Y, isweq f).
Defined.

Notation "X ≃ Y" := (weq X%type Y%type) : type_scope.

Definition pr1weq {X Y : UU} := pr1 : X ≃ Y -> (X -> Y).
Coercion pr1weq : weq >-> Funclass.

End PartA.
Module Export UniMath.
Module Export Foundations.
Module Export PartA.
Include UniMath_DOT_Foundations_DOT_PartA_WRAPPED.PartA.
End PartA.
Fixpoint isofhlevel (n : nat) (X : UU) : UU.
Admitted.

Definition isaprop := isofhlevel 1.

Definition funextsecStatement :=
  ∏ (T:UU) (P:T -> UU) (f g :∏ t:T, P t), f ~ g -> f = g.

Definition funextfunStatement :=
  ∏ (X Y:UU) (f g : X -> Y), f ~ g -> f = g.

Theorem funextfunImplication : funextsecStatement -> funextfunStatement.
Admitted.
Definition funextsec : funextsecStatement.
Admitted.

Definition funextfun := funextfunImplication (@funextsec).
Arguments funextfun {_ _} _ _ _.
Module Export Constr.

Module Export Pretype.
  Module Export Flags.
    Ltac2 Type t.

    Ltac2 @ external constr_flags : t := "rocq-runtime.plugins.ltac2" "constr_flags".

    Ltac2 @external set_allow_evars : bool -> t -> t
      := "rocq-runtime.plugins.ltac2" "pretype_flags_set_allow_evars".

    Ltac2 @external set_nf_evars : bool -> t -> t
      := "rocq-runtime.plugins.ltac2" "pretype_flags_set_nf_evars".

    Ltac2 Abbreviation open_constr_flags_with_tc :=
      set_nf_evars false (set_allow_evars true constr_flags).
  End Flags.

  Ltac2 Type expected_type.

  Ltac2 @ external expected_oftype : constr -> expected_type
    := "rocq-runtime.plugins.ltac2" "expected_oftype".

  Ltac2 @ external pretype : Flags.t -> expected_type -> preterm -> constr
    := "rocq-runtime.plugins.ltac2" "constr_pretype".

Definition hProp := total2 (λ X : UU, isaprop X).
Definition hProptoType := @pr1 _ _ : hProp -> UU.
Coercion hProptoType : hProp >-> UU.
Definition hSet : UU.
Admitted.
Definition pr1hSet : hSet -> UU.
Admitted.
Coercion pr1hSet: hSet >-> UU.
Definition natgth (n m : nat) : hProp.
Admitted.

Notation " x > y " := (natgth x y) : nat_scope.

Definition natlth (n m : nat) := m > n.

Notation " x < y " := (natlth x y) : nat_scope.

Ltac2 apply0 adv ev cb cl :=
  Std.apply adv ev cb cl.

Ltac2 Notation "apply"
  cb(list1(thunk(seq(open_constr, with_bindings)), ","))
  cl(opt(seq("in", ident, opt(seq("as", intropattern))))) :=
  apply0 true false cb cl.

Ltac2 exact1 ev c :=
  Control.enter (fun () =>
    let c :=
      Constr.Pretype.pretype
        (if ev then Constr.Pretype.Flags.open_constr_flags_with_tc else Constr.Pretype.Flags.constr_flags)
        (Constr.Pretype.expected_oftype (Control.goal()))
        c
    in
    Std.exact_no_check c).

Ltac2 Notation "exact" c(preterm) := exact1 false c.

Ltac2 Notation "intro" id(opt(ident)) mv(opt(move_location)) := Std.intro id mv.

Ltac2 Abbreviation refine := Control.refine.
Module Export UniMath_DOT_Foundations_DOT_All_WRAPPED.
Module Export All.
Export UniMath.Foundations.PartA.

End All.
Module Export UniMath.
Module Export Foundations.
Module Export All.
Include UniMath_DOT_Foundations_DOT_All_WRAPPED.All.
End All.
Definition precategory_ob_mor : UU.
exact (∑ ob : UU, ob -> ob -> UU).
Defined.
Definition make_precategory_ob_mor (ob : UU)(mor : ob -> ob -> UU) :
    precategory_ob_mor.
exact (tpair _ ob mor).
Defined.
Definition ob (C : precategory_ob_mor) : UU.
exact (@pr1 _ _ C).
Defined.
Coercion ob : precategory_ob_mor >-> UU.
Definition precategory_morphisms { C : precategory_ob_mor } :
       C ->  C -> UU.
exact (pr2 C).
Defined.

Declare Scope cat.

Local Open Scope cat.

Notation "a --> b" := (precategory_morphisms a b) : cat.
Definition precategory_id_comp (C : precategory_ob_mor) : UU.
exact ((∏ c : C, c --> c)
      ×
    (∏ a b c : C, a --> b -> b --> c -> a --> c)).
Defined.
Definition precategory_data : UU.
exact (∑ C : precategory_ob_mor, precategory_id_comp C).
Defined.
Definition make_precategory_data (C : precategory_ob_mor)
    (id : ∏ c : C, c --> c)
    (comp: ∏ a b c : C, a --> b -> b --> c -> a --> c)
  : precategory_data.
exact (tpair _ C (make_dirprod id comp)).
Defined.
Definition precategory_ob_mor_from_precategory_data (C : precategory_data) :
     precategory_ob_mor.
exact (pr1 C).
Defined.
Coercion precategory_ob_mor_from_precategory_data :
  precategory_data >-> precategory_ob_mor.
Definition is_precategory (C : precategory_data) : UU.
Admitted.

Definition precategory := total2 is_precategory.
Definition make_precategory (C : precategory_data) (H : is_precategory C)
  : precategory.
exact (tpair _ C H).
Defined.
Definition precategory_data_from_precategory (C : precategory) :
       precategory_data.
exact (pr1 C).
Defined.
Coercion precategory_data_from_precategory : precategory >-> precategory_data.
Definition has_homsets (C : precategory_ob_mor) : UU.
Admitted.

Definition category := ∑ C:precategory, has_homsets C.
Definition make_category C h : category := C,,h.
Definition category_to_precategory : category -> precategory.
exact (pr1).
Defined.
Coercion category_to_precategory : category >-> precategory.

Notation ℕ := nat.

Definition stn ( n : nat ) := ∑ m, m < n.

Notation "⟦ n ⟧" := (stn n) : stn.
Module Export Ltac2_DOT_Ltac2_WRAPPED.
Module Export Ltac2.

Export Ltac2.Init.

End Ltac2.
Module Export Ltac2_DOT_Ltac2.
Module Export Ltac2.
Module Export Ltac2.
Include Ltac2_DOT_Ltac2_WRAPPED.Ltac2.
End Ltac2.
Definition stnweq {n : nat}
  : stn n ⨿ unit ≃ stn (1 + n).
Admitted.

Definition extend_tuple
  {T : UU}
  {n : nat}
  (f : stn n → T)
  (last : T)
  : stn (S n) → T.
Admitted.

Lemma extend_tuple_inl
  {T : UU}
  {n : nat}
  (f : stn n → T)
  (last : T)
  (i : stn n)
  : extend_tuple f last (stnweq (inl i)) = f i.
Admitted.

Lemma extend_tuple_inr
  {T : UU}
  {n : nat}
  (f : stn n → T)
  (last : T)
  (t : unit)
  : extend_tuple f last (stnweq (inr t)) = last.
Admitted.
Import UniMath.Foundations.All.

Section IndexedSetCategory.

  Context (I : UU).

  Definition indexed_set_cat
    : category.
  Proof.
    use make_category.
    -
 use make_precategory.
      +
 use make_precategory_data.
        *
 use make_precategory_ob_mor.
          --
 exact (I → hSet).
          --
 intros X Y.
            exact (∏ i, X i → Y i).
        *
 intros X i.
          apply idfun.
        *
 intros X Y Z f g i.
          exact (funcomp (f i) (g i)).
      +
 admit.
    -
 admit.
  Defined.

End IndexedSetCategory.
Definition var_ax
    (T : indexed_set_cat nat)
    (n : nat)
    (i : stn n)
    : UU.
exact (T n).
Defined.
Definition subst_ax
    (T : indexed_set_cat nat)
    (m n : nat)
    (f : T m)
    (g : stn m → T n)
    : UU.
exact (T n).
Defined.

Declare Scope algebraic_theories.
Local Open Scope algebraic_theories.
Definition algebraic_theory_data : UU.
Admitted.
Definition algebraic_theory_data_to_function
  (T : algebraic_theory_data)
  : nat → hSet.
Admitted.

Coercion algebraic_theory_data_to_function : algebraic_theory_data >-> Funclass.
Definition var
  {T : algebraic_theory_data}
  {n : nat}
  (i : stn n)
  : var_ax T n i.
Admitted.
Definition subst
  {T : algebraic_theory_data}
  {m n : nat}
  (f : T m)
  (g : stn m → T n)
  : subst_ax T m n f g.
Admitted.

Notation "f • g" :=
  (subst f g)
  (at level 35) : algebraic_theories.
Definition algebraic_theory : UU.
Admitted.
Coercion algebraic_theory_to_algebraic_theory_data (T : algebraic_theory)
  : algebraic_theory_data.
Admitted.
Definition var_subst_ax
  (T : algebraic_theory_data)
  (m n : nat)
  (i : stn m)
  (f : stn m → T n)
  : UU.
exact (var i • f = f i).
Defined.
Definition subst_var_ax
  (T : algebraic_theory_data)
  (n : nat)
  (f : T n)
  : UU.
exact (f • var = f).
Defined.
Definition var_subst
  (T : algebraic_theory)
  {m n : nat}
  (i : stn m)
  (f : stn m → T n)
  : var_subst_ax (T : algebraic_theory_data) m n i f.
Admitted.
Definition subst_var
  (T : algebraic_theory)
  {n : nat}
  (f : T n)
  : subst_var_ax (T : algebraic_theory_data) n f.
Admitted.
Definition inflate {T : algebraic_theory_data} {n : nat} (f : T n) : T (S n).
Admitted.

Lemma subst_inflate (T : algebraic_theory) {m n : nat} (f : T m) (g : stn (S m) → T n)
  : subst (inflate f) g = subst f (λ i, g (stnweq (inl i))).
Admitted.
Definition abs_ax
    (T : algebraic_theory)
    (n : nat)
    (f : T (S n))
    : UU.
exact (T n).
Defined.
Definition lambda_theory_data : UU.
Admitted.
Coercion lambda_theory_data_to_algebraic_theory (L : lambda_theory_data)
  : algebraic_theory.
Admitted.
Definition abs {L : lambda_theory_data} {n : nat} (f : L (S n)) : abs_ax L n f.
Admitted.
Definition lambda_theory : UU.
Admitted.
Coercion lambda_theory_to_lambda_theory_data (L : lambda_theory) : lambda_theory_data.
Admitted.
Definition has_β (L : lambda_theory) : UU.
Admitted.
Definition app {L : lambda_theory_data} {n : nat} (f g : L n) : L n.
Admitted.

Lemma subst_app (L : lambda_theory) {m n : nat} (f g : L m) (h : stn m → L n)
  : subst (app f g) h = app (subst f h) (subst g h).
Admitted.

Definition beta_equality (L : lambda_theory) (H : has_β L) {n : nat} (f : L (S n)) (g : L n)
  : app (abs f) g = subst f (extend_tuple var g).
Admitted.
Import Ltac2.Ltac2.
Local Open Scope stn.
Definition union_arrow
  {L : lambda_theory}
  {n : nat}
  (a b : L n)
  : L n.
exact (abs
    (app
      (app
        (var (stnweq (inr tt)))
        (inflate a))
      (inflate b))).
Defined.

Lemma app_union_arrow
  (L : lambda_theory)
  (Lβ : has_β L)
  {n : nat}
  (a b c : L n)
  : app (union_arrow a b) c = app (app c a) b.
Proof.
  refine '(beta_equality _ Lβ _ _ @ _).
  refine '(subst_app _ _ _ _ @ _).
  refine '(maponpaths (λ x, (app x _)) (subst_app _ _ _ _) @ _).
  refine '(maponpaths (λ x, (app _ x)) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (app (app x _) _)) (var_subst _ _ _) @ _).
  refine '(maponpaths (λ x, (app (app _ x) _)) (subst_inflate _ _ _) @ _).
  refine '(maponpaths (λ x, (app (app x _) _)) (extend_tuple_inr _ _ _) @ _).
  refine '(_ @ maponpaths (λ x, (app (app _ x) _)) (subst_var _ _)).
  refine '(_ @ maponpaths (λ x, (app _ x)) (subst_var _ _)).

  refine '(maponpaths (λ x, (app (app _ (_ • x)) _)) _ @ maponpaths (λ x, (app _ (_ • x))) _);
    apply funextfun;
    intro i;
    apply extend_tuple_inl.
Qed.

End Ltac2.
End Ltac2_DOT_Ltac2.
End Ltac2_DOT_Ltac2_WRAPPED.
End Foundations.
End UniMath.
End UniMath_DOT_Foundations_DOT_All_WRAPPED.
End Pretype.
End Constr.
End Foundations.
End UniMath.
End UniMath_DOT_Foundations_DOT_PartA_WRAPPED.
End Foundations.
End UniMath.
End UniMath_DOT_Foundations_DOT_Preamble_WRAPPED.
End Control.
End Foundations.
End UniMath.
End UniMath_DOT_Foundations_DOT_Init_WRAPPED.
