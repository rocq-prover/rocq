Set Universe Polymorphism.
Unset Collapse Sorts ToType.
Set Printing Universes.

Module Reduction.

  Definition qsort := Univ.
  (* qsort@{α ; u |} = Univ@{α ; u} : Univ@{u+1} *)

  Definition qsort' : Univ := Univ.
  (* qsort'@{α ; u u0 |} = Univ@{α ; u0} : Univ@{u} *)

  Monomorphic Universe U.

  Definition tU := Type@{U}.
  Definition qU := qsort@{Type ; U}.

  Definition q1 := Eval lazy in qU.
  Check eq_refl : q1 = tU.

  Definition q2 := Eval vm_compute in qU.
  Check eq_refl : q2 = tU.

  Definition q3 := Eval native_compute in qU.
  Check eq_refl : q3 = tU.

  Definition exfalso (A:Univ) (H:False) : A := match H with end.
  (* exfalso@{α ; u |} : forall A : Univ@{α ; _}, False -> A *)

  Definition exfalsoVM := Eval vm_compute in exfalso@{Type;Set}.
  Definition exfalsoNative := Eval native_compute in exfalso@{Type;Set}.

  Fixpoint iter (A:Univ) (f:A -> A) n x :=
    match n with
    | 0 => x
    | S k => iter A f k (f x)
    end.
  (* iter@{α ; u |} : forall (A : Univ@{α ; u}) (_ : forall _ : A, A) (_ : nat) (_ : A), A *)

  Definition iterType := Eval lazy in iter@{Type;_}.
  Definition iterSProp := Eval lazy in iter@{SProp;_}.

End Reduction.

Module Conversion.

  Inductive Box (A:Univ) := box (_:A).
  (* Box@{α α0 ; u |} (A : Univ@{α ; u}) : Univ@{α0 ; u} *)

  Definition t1 (A:Univ) (x y : A) := box _ x.
  (* t1@{α α0 ; u |} : forall (A : Univ@{α ; u}) (_ : A) (_ : A), Box@{α α0 ; u} A *)
  Definition t2 (A:Univ) (x y : A) := box _ y.
  (* t2@{α α0 ; u |} : forall (A : Univ@{α ; u}) (_ : A) (_ : A), Box@{α α0 ; u} A *)

  Definition t1' (A:Univ) (x y : A) := x.
  (* t1'@{α ; u |} : forall (A : Univ@{α ; u}) (_ : A) (_ : A), A *)
  Definition t2' (A:Univ) (x y : A) := y.

  Fail Check eq_refl : t1 nat = t2 nat.
  Fail Check eq_refl : t1' nat = t2' nat.

  Check fun A:SProp => eq_refl : t1 A = t2 A.
  (* : forall A : SProp,
       @eq (forall (_ : A) (_ : A), Box@{SProp Type ; sort_poly_elab.475} A)
         (t1@{SProp Type ; sort_poly_elab.475} A)
         (t2@{SProp Type ; sort_poly_elab.475} A) *)

  Check fun A:SProp => eq_refl : box _ (t1' A) = box _ (t2' A).
  (* : forall A : SProp,
       @eq
         (Box@{SProp Type ; sort_poly_elab.479} (forall (_ : A) (_ : A), A))
         (box@{SProp Type ; sort_poly_elab.479} (forall (_ : A) (_ : A), A)
            (t1'@{SProp ; sort_poly_elab.480} A))
         (box@{SProp Type ; sort_poly_elab.479} (forall (_ : A) (_ : A), A)
            (t2'@{SProp ; sort_poly_elab.482} A)) *)

  Definition ignore {A:Univ} (x:A) := tt.
  (* ignore@{α ; u |} : forall {A : Univ@{α ; u}} (_ : A), unit *)

  Definition unfold_ignore (A:Univ) : ignore (t1 A) = ignore (t2 A) := eq_refl.
  (* unfold_ignore@{α α0 α1 ; u |} : forall A : Univ@{α ; u},
       @eq unit
         (@ignore@{α0 ; u} (forall (_ : A) (_ : A), Box@{α α0 ; u} A)
            (t1@{α α0 ; u} A))
         (@ignore@{α1 ; u} (forall (_ : A) (_ : A), Box@{α α1 ; u} A)
            (t2@{α α1 ; u} A)) *)

  Definition t (A:SProp) := Eval lazy in t1 A.
  (* t@{α ; u |} : forall (A : SProp) (_ : A) (_ : A), Box@{SProp α ; u} A *)

  Axiom v : forall (A:Univ), bool -> A.
  Fail Check fun P (x:P (v@{Type;_} nat true)) => x : P (v nat false).
  Check fun (A:SProp) P (x:P (v A true)) => x : P (v A false).
    (* : forall (A : SProp) (P : A -> Type@{sort_poly_elab.105}),
       P (v@{SProp ; sort_poly_elab.104} A true) ->
       P (v@{SProp ; sort_poly_elab.106} A false) *)
End Conversion.

Module Inference.
  Definition zog (A:Univ) := A.
  (* zog@{α ; u |} : Univ@{α ; _} -> Univ@{α ; _} *)

  (* implicit instance of zog gets a variable which then gets unified with s from the type of A *)
  Definition zag (A:Univ) := zog A.
  (* zag@{α ; u |} : Univ@{α ; _} -> Univ@{α ; _} *)

  (* implicit type of A gets unified to Univ@{s;u} *)
  Definition zig A := zog A.
  (* zig@{α ; u |} : Univ@{α ; _} -> Univ@{α ; _} *)

  (* different manually bound sort variables don't unify *)
  Fail Definition zog'@{s s'; |} (A:Univ@{s;Set}) := zog@{s';Set} A.
End Inference.

Module Inductives.
  Inductive implicit :=.
  (* implicit@{α ; u} : Univ@{α ; _} *)

  Inductive foo1 : Univ := .
  (* foo1@{α ; u |} : Univ@{α ; _} :=  . *)
  Fail Check foo1_sind.
  (* The reference foo1_sind was not found in the current environment. Did you mean bool_sind, prod_sind, or_sind or bool_ind? *)

  (* Fails if constraints cannot be extended *)
  Fail Definition foo1_False@{s;+|} (x : foo1@{s;_}) : False := match x return False with end.
  (* Elimination constraints are not implied by the ones declared: s -> Prop *)

  (* Explicitly allowing extending the constraints *)
  Definition foo1_False@{s;+|+} (x : foo1@{s;_}) : False := match x return False with end.
  (* s ; u |= s -> Prop *)

  (* Fully implicit qualities and constraints *)
  Definition foo1_False' (x : foo1) : False := match x return False with end.
  (* foo1_False'@{α ; u |} : foo1@{α ; u} -> False *)
  (* α ; u |= α -> Prop *)

  Inductive foo2 := Foo2 : Univ -> foo2.
  (* foo2@{α ; u |} : Univ@{α ; u+1} *)
  Fail Check foo2_rect.
  (* The reference foo2_rect was not found in the current environment. Did you mean bool_rect, sig2_rect, prod_rect, ex2_rect or bool_rec? *)

  Inductive foo3 A := Foo3 : A -> foo3 A.
  (* foo3@{α α0 ; u |} (A : Univ@{α0 ; u}) : Univ@{α ; u} *)
  Fail Check foo3_rect.
  (* The reference foo3_rect was not found in the current environment. Did you mean bool_rect, prod_rect or bool_rec? *)

  Inductive foo5 (A : Univ) : Prop := Foo5 (_ : A).
  (* foo5@{α ; u} : Univ@{α ; u} -> Prop *)

  Definition foo5_ind' : forall (A : Univ) (P : Prop), (A -> P) -> foo5 A -> P
    := foo5_ind.

  Definition foo5_Prop_rect (A:Prop) (P:foo5 A -> Univ)
    (H : forall a, P (Foo5 A a))
    (f : foo5 A)
    : P f
    := match f with Foo5 _ a => H a end.
  (* foo5_Prop_rect@{α ; u} :
    forall (A : Prop) (P : foo5@{Type ; Set} A -> Univ@{α ; u}),
    (forall a : A, P (Foo5@{Type ; Set} A a)) -> forall f : foo5@{Type ; Set} A, P f *)
  (* α ; u |= Prop -> α *)

  Definition foo5_Prop_rect' (A : Prop) (P : foo5 A -> Univ)
    (H : forall a, P (Foo5 A a))
    (f : foo5@{Prop;_} A)
    : P f
    := match f with Foo5 _ a => H a end.
  (* foo5_Prop_rect'@{α ; u} :
    forall (A : Prop) (P : foo5@{Prop ; Set} A -> Univ@{α ; u}),
    (forall a : A, P (Foo5@{Prop ; Set} A a)) -> forall f : foo5@{Prop ; Set} A, P f *)
  (* α ; u |=  *)

  Inductive foo6 : Univ := Foo6.
  Fail Check foo6_sind.
  (* The reference foo6_sind was not found in the current environment. Did you mean foo5_sind, foo5_ind, bool_sind, prod_sind, or_sind, foo5_ind' or bool_ind? *)

  Definition foo6_rect (P:foo6 -> Univ)
    (H : P Foo6)
    (f : foo6)
    : P f
    := match f with Foo6 => H end.
  (* foo6_rect@{α α0 ; u u0} : forall P : foo6@{α0 ; u} -> Univ@{α ; u0}, P Foo6@{α0 ; u} -> forall f : foo6@{α0 ; u}, P f *)
  (* α α0 ; u u0 |= α0 -> α *)

  Definition foo6_prop_rect (P:foo6 -> Univ)
    (H : P Foo6)
    (f : foo6@{Prop;_})
    : P f
    := match f with Foo6 => H end.
  (* foo6_prop_rect@{α ; u u0} : forall P : foo6@{Prop ; u} -> Univ@{α ; u0}, P Foo6@{Prop ; u} -> forall f : foo6@{Prop ; u}, P f *)
  (* α ; u u0 |=  *)

  Definition foo6_type_rect (P:foo6 -> Univ)
    (H : P Foo6)
    (f : foo6@{Type;_})
    : P f
    := match f with Foo6 => H end.
  (* foo6_type_rect@{α ; u u0} : forall P : foo6@{Type ; u} -> Univ@{α ; u0}, P Foo6@{Type ; u} -> forall f : foo6@{Type ; u}, P f *)
  (* α ; u u0 |=  *)

  Inductive foo7 : Univ := Foo7_1 | Foo7_2.
  Fail Check foo7_sind.
  Fail Check foo7_ind.

  Definition foo7_prop_ind (P:foo7 -> Prop)
    (H : P Foo7_1) (H' : P Foo7_2)
    (f : foo7@{Prop;})
    : P f
    := match f with Foo7_1 => H | Foo7_2 => H' end.

  Definition foo7_prop_rect (P:foo7 -> Univ)
    (H : P Foo7_1) (H' : P Foo7_2)
    (f : foo7@{Prop;})
    : P f
    := match f with Foo7_1 => H | Foo7_2 => H' end.

  (*********************************************)
  (*                 SIGMA                     *)
  (*********************************************)
  Inductive sigma (A:Univ) (B:A -> Univ) : Univ
    := pair : forall x : A, B x -> sigma A B.
  (* Inductive sigma@{α α0 α1 ; u u0 |} (A : Univ@{α ; u}) (B : A -> Univ@{α0 ; u0}) : Univ@{α1 ; max(u,u0)} *)

  Definition sigma_srect A B
    (P : sigma A B -> Univ)
    (H : forall x b, P (pair _ _ x b))
    (s:sigma A B)
    : P s
    := match s with pair _ _ x b => H x b end.
  (* α α0 α1 α2 ; u u0 u1 |= α2 -> α *)

  (* Elimination constraints are added *)
  Definition pr1 {A B} (s:sigma A B) : A
    := match s with pair _ _ x _ => x end.
  (* α α0 α1 ; u u0 |= α1 -> α *)

  Definition pr2 {A B} (s:sigma A B) : B (pr1 s)
    := match s with pair _ _ _ y => y end.
  (* α α0 α1 ; u u0 |= α1 -> α
                       α1 -> α0 *)


  Definition π1 {A:Univ} {P:A -> Univ} (p : sigma@{Type _ _;_ _ _} A P) : A :=
    match p return A with pair _ _ a _ => a end.
  (* α α0 ; u u0 |= α0 -> Type *)

  (*********************************************)
  (*                   EQ                      *)
  (*********************************************)
  Inductive seq (A:Univ) (a:A) : A -> Prop := seq_refl : seq A a a.
  (* Inductive seq@{α ; u |} (A : Univ@{α ; u}) (a : A) : A -> Prop *)
  Arguments seq_refl {_ _}.

  Definition eta A B (s:sigma A B) : seq _ s (pair A B (pr1 s) (pr2 s)).
  Proof.
    destruct s. simpl. reflexivity.
  Qed.

  (*********************************************)
  (*                   SUM                     *)
  (*********************************************)
  Inductive sum (A B : Univ) : Univ :=
  | inl : A -> sum A B
  | inr : B -> sum A B.
  (* sum@{α α0 α1 ; u u0} : Univ@{α ; u} -> Univ@{α0 ; u0} -> Univ@{α1 ; max(Set,u,u0)} *)
  (* α α0 α1 ; u u0 |=  *)

  Arguments inl {A B} _ , [A] B _.
  Arguments inr {A B} _ , A [B] _.

  (* Elimination constraint left explicitly empty. Definition fails because of missing constraint. *)
  Fail Definition sum_elim@{sl sr s0 s0';ul ur v|}
    (A : Univ@{sl;ul}) (B : Univ@{sr;ur}) (P : sum@{sl sr s0;ul ur} A B -> Univ@{s0';v})
    (fl : forall a, P (inl a)) (fr : forall b, P (inr b)) (x : sum@{sl sr s0;ul ur} A B) :=
    match x with
    | inl a => fl a
    | inr b => fr b
    end.
  (* The command has indeed failed with message:
  Elimination constraints are not implied by the ones declared: s0->s0' *)

  (* Leaving them implicit *)
  (* FIXME: Would be nicer to have P's sort last instead of first *)
  Definition sum_elim (A B : Univ) (P : sum A B -> Univ)
    (fl : forall a, P (inl a)) (fr : forall b, P (inr b)) (x : sum A B) :=
    match x with
    | inl a => fl a
    | inr b => fr b
    end.
  (* α α0 α1 α2 ; u u0 u1 |= α2 -> α *)

  Definition sum_sind := sum_elim@{SProp Type Type Type;_ _ _ _}.
  Definition sum_rect := sum_elim@{Type Type Type Type;_ _ _ _}.
  Definition sum_ind := sum_elim@{Prop Type Type Type;_ _ _ _}.

  Definition or_ind := sum_elim@{Prop Prop Prop Prop;_ _ _ _}.
  Definition or_sind := sum_elim@{SProp Prop Prop Prop;_ _ _ _}.
  Fail Definition or_rect := sum_elim@{Type Prop Prop Prop;_ _ _ _}.
  (* The command has indeed failed with message:
  The quality constraints are inconsistent: cannot enforce Prop -> Type because it would identify Type and Prop which is inconsistent.
  This is introduced by the constraints Prop -> Type *)

  Definition sumor := sum@{Type Prop Type; _ _ _}.

  Definition sumor_sind := sum_elim@{SProp Prop Type Type; _ _ _ _}.
  Definition sumor_rect := sum_elim@{Type Prop Type Type; _ _ _ _}.
  Definition sumor_ind := sum_elim@{Prop Prop Type Type; _ _ _ _}.

  (* Implicit qualities and constraints are elaborated *)
  Definition idT (A B : Univ) (x : sum A B)
    : sum@{_ _ Type; _ _ _} A B :=
    match x with
    | inl a => inl a
    | inr b => inr b
    end.
  (* α α0 α1 ; u u0 |= α -> Type *)

  (* Implicit qualities and constraints are elaborated *)
  Definition idPsr (A B : Univ) (x : sum A B)
    : sum@{_ _ Prop; _ _ _} A B :=
    match x with
    | inl a => inl a
    | inr b => inr b
    end.
  (* α α0 α1 ; u u0 |= α -> Prop *)

  (* Implicit qualities and constraints are elaborated *)
  Definition idS (A B : Univ) (x : sum A B)
    : sum@{_ _ SProp; _ _ _} A B :=
    match x with
    | inl a => inl a
    | inr b => inr b
    end.
  (* α α0 α1 ; u u0 |= α -> Prop *)

  (* Implicit qualities and constraints are elaborated *)
  Definition idV (A B : Univ) (x : sum A B)
    : sum A B :=
    match x with
    | inl a => inl a
    | inr b => inr b
    end.
  (* α α0 α1 α2 ; u u0 u1 |= α -> α2 *)

  Fail Compute idV@{Prop Type Prop Type;Set Set Set} (inl I).
  (* The quality constraints are inconsistent: cannot enforce Prop -> Type because it would identify Type and Prop which is inconsistent.
      This is introduced by the constraints Prop -> Type *)

  (*********************************************)
  (*                  LIST                     *)
  (*********************************************)
  Inductive list (A : Univ) : Univ :=
  | nil : list A
  | cons : A -> list A -> list A.

  Arguments nil {A}.
  Arguments cons {A} _ _.

  Definition list_elim
    (A : Univ) (P : list A -> Univ)
    (fn : P nil) (fc : forall (x : A) (l : list A), P l -> P (cons x l)) :=
    fix F (l : list A) : P l :=
      match l with
      | nil => fn
      | cons x l => fc x l (F l)
      end.
  (* α α0 α1 ; u u0 |= α1 -> α *)

  Fixpoint list_idT {A : Univ} (l : list A) : list@{_ Type;_ _} A :=
    match l with
    | nil => nil
    | cons x l => cons x (list_idT l)
    end.
  (* α α0 ; u |= α -> Type *)

  Fixpoint list_idP {A : Univ} (l : list A) : list@{_ Prop;_ _} A :=
    match l with
    | nil => nil
    | cons x l => cons x (list_idP l)
    end.
  (* α α0 ; u |= α -> Prop *)

  Fixpoint list_idS {A : Univ} (l : list A) : list@{_ SProp;_ _} A :=
    match l with
    | nil => nil
    | cons x l => cons x (list_idS l)
    end.
  (* α α0 ; u |= α -> SProp *)

  Fixpoint map A B f (l : list A) : list B :=
    match l with
    | nil => nil
    | cons x l' => cons (f x) (map A B f l')
    end.
  (* map@{α α0 α1 α2 ; u u0} :
      forall (A : Type@{α ; u}) (B : Type@{α1 ; u0}) (_ : forall _ : A, B)
      (_ : list@{α α0 ; u} A), list@{α1 α2 ; u0} B *)
  (* α α0 α1 α2 ; u u0 |= α0 -> α2 *)

  (*********************************************)
  (*                  FALSE                    *)
  (*********************************************)
  Inductive False' : Univ :=.
  (* False'@{α ; u} : Univ@{α ; u} *)

  Definition False'_False (x : False') : False := match x return False with end.
  (* α ; u |= α -> Prop *)

  (*********************************************)
  (*                  BOOL                     *)
  (*********************************************)
  Inductive bool : Univ := true | false.

  Definition bool_to_Prop (b : bool) : Prop.
  Proof.
    destruct b.
    - exact True.
    - exact False.
  Defined.
  (* α ;  |= α -> Type *)

  Definition bool_to_True_conj (b : bool) : True \/ True.
  Proof.
    destruct b.
    - exact (or_introl I).
    - exact (or_intror I).
  Defined.
  (* α ;  |= α -> Prop *)

  (* Using Program *)
  Program Definition bool_to_Prop' (b : bool) : Prop := _.
  Next Obligation.
    intro b; destruct b.
    - exact True.
    - exact False.
  Defined.
  (* α ;  |= α -> Type *)

  #[universes(polymorphic=no)]
  Sort Test.
  (* Sort variables not instantiated *)
  Fail Check (match true@{Test;} return ?[P] with true => tt | false => tt end).
  (* Incorrect elimination of "true@{Test ; }" in the inductive type "bool@{Test ; }":
  the return type has sort "Set" while it should be in a sort Test eliminates to.
  Elimination of a sort polymorphic inductive object instantiated to a variable sort quality
  is only allowed on itself or with an explicit elimination constraint to the target sort. *)

  (*********************************************)
  (*                  UNIT                     *)
  (*********************************************)
  Inductive unit : Univ := tt.
  (* unit@{α ; u} : Univ@{α ; u} *)

  (*********************************************)
  (*                  MISC                     *)
  (*********************************************)
  (* Interactive definition *)
  Inductive FooNat :=
  | FO : FooNat
  | FS : FooNat -> FooNat.

  Definition Foo (n : FooNat) : FooNat.
    destruct n.
    - exact FO.
    - exact FO.
  Defined.

  Check Foo@{Type Prop;}.
  Fail Check Foo@{Prop Type;}.
End Inductives.

Module Records.

  Set Primitive Projections.
  Set Warnings "+records".

  (* the SProp instantiation may not be primitive so the whole thing must be nonprimitive *)
  Fail Record R1 : Univ := {}.

  (* the Type instantiation may not be primitive *)
  Fail Record R2 (A:SProp) : Univ := { R2f1 : A }.

  (* R3@{SProp Type;} may not be primitive  *)
  Fail Record R3 (A:Univ) : Univ := { R3f1 : A }.

  Record R4@{s; |} (A:Univ@{s;Set}) : Univ@{s;Set} := { R4f1 : A}.

  (* non SProp instantiation must be squashed *)
  Fail Record R5 (A:Univ) : SProp := { R5f1 : A}.
  Fail #[warnings="-non-primitive-record"]
    Record R5 (A:Univ) : SProp := { R5f1 : A}.
  (* This expression would enforce an elimination constraint between SProp and
  β0 that is not allowed. *)

  Fail #[warnings="-non-primitive-record,-cannot-define-projection"]
    Record R5 (A:Univ) : SProp := { R5f1 : A}.
  (* This expression would enforce an elimination constraint between SProp and
  β0 that is not allowed. *)

  Record R6 (A:Univ) : Set := { R6f1 : A; R6f2 : nat }.
  (* R6@{α ; } : forall _ : Univ@{α ; Set}, Set *)

  Check fun (A:SProp) (x y : R6 A) =>
          eq_refl : Conversion.box _ x.(R6f1 _) = Conversion.box _ y.(R6f1 _).
  Fail Check fun (A:Prop) (x y : R6 A) =>
          eq_refl : Conversion.box _ x.(R6f1 _) = Conversion.box _ y.(R6f1 _).
  Fail Check fun (A:SProp) (x y : R6 A) =>
          eq_refl : Conversion.box _ x.(R6f2 _) = Conversion.box _ y.(R6f2 _).

  (* Elimination constraints are accumulated by fields, even on independent fields *)
  #[projections(primitive=no)] Record R7 (A:Univ) := { R7f1 : A; R7f2 : nat }.
  (* Record R7@{α α0 ; u |} (A : Univ@{α ; u}) : Univ@{α0 ; max(Set,u)}  *)
  (* R7f1@{α α0 ; u |} : forall A : Univ@{α ; u}, R7@{α α0 ; u} A -> A
      α α0 ; u |= α0 -> α *)
  (* R7f2@{α α0 ; u |} : forall A : Univ@{α ; u}, R7@{α α0 ; u} A -> nat
      α α0 ; u |= α0 -> α
                  α0 -> Type *)

  (* sigma as a primitive record works better *)
  Record Rsigma@{s;u v|} (A:Univ@{s;u}) (B:A -> Univ@{s;v}) : Univ@{s;max(u,v)}
    := Rpair { Rpr1 : A; Rpr2 : B Rpr1 }.

  (* match desugared to primitive projections using definitional eta *)
  Definition Rsigma_srect A B
    (P : Rsigma A B -> Univ)
    (H : forall x b, P (Rpair _ _ x b))
    (s:Rsigma A B)
    : P s
    := match s with Rpair _ _ x b => H x b end.
  (* Rsigma_srect@{α α0 ; u u0 u1 |} : forall (A : Univ@{α0 ; _}) (B : A -> Univ@{α0 ; _})
         (P : Rsigma A B -> Univ@{α ; _}),
       (forall (x : A) (b : B x), P {| Rpr1 := x; Rpr2 := b |}) ->
       forall s : Rsigma A B, P s *)

  (* sort polymorphic exists (we could also make B sort poly)
     can't be a primitive record since the first projection isn't defined at all sorts *)
  Inductive sexists (A:Univ) (B:A -> Prop) : Prop
    := sexist : forall a:A, B a -> sexists A B.

  (* we can eliminate to Prop *)
  Check sexists_ind.

  Unset Primitive Projections.

  (* Elimination constraints are accumulated by fields *)
  Record R8 := {
    R8f1 : Univ;
    R8f2 : R8f1
  }.
  (* Record R8@{α α0 ; u |} : Univ@{α ; u+1}. *)
  (* R8f1@{α α0 ; u |} : R8@{α α0 ; u} -> Univ@{α0 ; u}
      α α0 ; u |= α -> Type *)
  (* R8f2@{α α0 ; u |} : forall r : R8@{α α0 ; u}, R8f1@{α α0 ; u} r
      α α0 ; u |= α -> α0
                  α -> Type *)
End Records.

Module Class.
  Class MyClass (A : Univ) : Univ := {
    my_field : A
  }.

  Inductive unit : Univ := tt.

  Instance MyInstance : MyClass unit := { my_field := tt }.

  Program Instance MyProgramInstance : MyClass unit.
  Next Obligation.
    exact tt.
  Defined.

  #[refine]
  Instance MyRefineInstance : MyClass unit := { my_field := _ }.
  exact tt.
  Defined.

  Instance MyInteractiveInstance : MyClass unit.
  Proof. constructor. exact tt. Defined.

  Axiom (MyAxiomaticInstance : MyClass unit).
  Existing Instance MyAxiomaticInstance.

  Inductive MyInductive := mkInductive.

  Existing Class MyInductive.

End Class.
