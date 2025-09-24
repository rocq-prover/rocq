Set Universe Polymorphism.
Unset Collapse Sorts ToType.
Set Printing Universes.
Set Printing Sort Qualities.
Set Printing All.
Set Warnings "-native-compiler-disabled".

Module Reduction.

  Definition qsort := Type.
  (* qsort@{α ; u |} = Type@{α ; u} : Type@{u+1} *)
  About qsort.

  Definition qsort' : Type := Type.
  (* qsort'@{α ; u u0 |} = Type@{α ; u0} : Type@{u} *)
  About qsort'.

  Monomorphic Universe U.

  Definition tU := Type@{U}.
  Definition qU := qsort@{Type ; U}.

  Definition q1 := Eval lazy in qU.
  Check eq_refl : q1 = tU.

  Definition q2 := Eval vm_compute in qU.
  Check eq_refl : q2 = tU.

  Definition q3 := Eval native_compute in qU.
  Check eq_refl : q3 = tU.

  Definition exfalso (A:Type) (H:False) : A := match H with end.
  (* exfalso@{α ; u |} : forall A : Type@{α ; _}, False -> A *)
  About exfalso.

  Definition exfalsoVM := Eval vm_compute in exfalso@{Type;Set}.
  Definition exfalsoNative := Eval native_compute in exfalso@{Type;Set}.

  Fixpoint iter (A:Type) (f:A -> A) n x :=
    match n with
    | 0 => x
    | S k => iter A f k (f x)
    end.
  (* iter@{α ; u |} : forall (A : Type@{α ; u}) (_ : forall _ : A, A) (_ : nat) (_ : A), A *)
  About iter.

  Definition iterType := Eval lazy in iter@{Type;_}.
  Definition iterSProp := Eval lazy in iter@{SProp;_}.

End Reduction.

Module Conversion.

  Inductive Box (A:Type) := box (_:A).
  (* Box@{α α0 ; u |} (A : Type@{α ; u}) : Type@{α0 ; u} *)
  About Box.

  Definition t1 (A:Type) (x y : A) := box _ x.
  (* t1@{α α0 ; u |} : forall (A : Type@{α ; u}) (_ : A) (_ : A), Box@{α α0 ; u} A *)
  About t1.

  Definition t2 (A:Type) (x y : A) := box _ y.
  (* t2@{α α0 ; u |} : forall (A : Type@{α ; u}) (_ : A) (_ : A), Box@{α α0 ; u} A *)
  About t2.

  Definition t1' (A:Type) (x y : A) := x.
  (* t1'@{α ; u |} : forall (A : Type@{α ; u}) (_ : A) (_ : A), A *)
  About t1'.

  Definition t2' (A:Type) (x y : A) := y.
  About t2'.

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

  Definition ignore {A:Type} (x:A) := tt.
  (* ignore@{α ; u |} : forall {A : Type@{α ; u}} (_ : A), unit *)
  About ignore.

  Definition unfold_ignore (A:Type) : ignore (t1 A) = ignore (t2 A) := eq_refl.
  (* unfold_ignore@{α α0 α1 ; u |} : forall A : Type@{α ; u},
       @eq unit
         (@ignore@{α0 ; u} (forall (_ : A) (_ : A), Box@{α α0 ; u} A)
            (t1@{α α0 ; u} A))
         (@ignore@{α1 ; u} (forall (_ : A) (_ : A), Box@{α α1 ; u} A)
            (t2@{α α1 ; u} A)) *)
  About unfold_ignore.

  Definition t (A:SProp) := Eval lazy in t1 A.
  (* t@{α ; u |} : forall (A : SProp) (_ : A) (_ : A), Box@{SProp α ; u} A *)
  About t.

  Axiom v : forall (A:Type), bool -> A.
  About v.
  Fail Check fun P (x:P (v@{Type;_} nat true)) => x : P (v nat false).
  Check fun (A:SProp) P (x:P (v A true)) => x : P (v A false).
    (* : forall (A : SProp) (P : A -> Type@{sort_poly_elab.105}),
       P (v@{SProp ; sort_poly_elab.104} A true) ->
       P (v@{SProp ; sort_poly_elab.106} A false) *)
End Conversion.

Module Inference.
  Definition zog (A:Type) := A.
  (* zog@{α ; u |} : Type@{α ; _} -> Type@{α ; _} *)
  About zog.

  (* implicit instance of zog gets a variable which then gets unified with s from the type of A *)
  Definition zag (A:Type) := zog A.
  (* zag@{α ; u |} : Type@{α ; _} -> Type@{α ; _} *)
  About zag.

  (* implicit type of A gets unified to Type@{s;u} *)
  Definition zig A := zog A.
  (* zig@{α ; u |} : Type@{α ; _} -> Type@{α ; _} *)
  About zig.

  (* different manually bound sort variables don't unify *)
  Fail Definition zog'@{s s'; |} (A:Type@{s;Set}) := zog@{s';Set} A.
End Inference.

Module Inductives.
  Inductive implicit :=.
  (* implicit@{α ; u} : Type@{α ; _} *)
  About implicit.

  Inductive foo1 : Type := .
  (* foo1@{α ; u |} : Type@{α ; _} :=  . *)
  About foo1.
  Fail Check foo1_sind.
  (* The reference foo1_sind was not found in the current environment. Did you mean bool_sind, prod_sind, or_sind or bool_ind? *)

  (* Fails if constraints cannot be extended *)
  Fail Definition foo1_False@{s;+|} (x : foo1@{s;_}) : False := match x return False with end.
  (* Elimination constraints are not implied by the ones declared: s -> Prop *)

  (* Explicitly allowing extending the constraints *)
  Definition foo1_False@{s;+|+} (x : foo1@{s;_}) : False := match x return False with end.
  (* s ; u |= s -> Prop *)
  About foo1_False.

  (* Fully implicit qualities and constraints *)
  Definition foo1_False' (x : foo1) : False := match x return False with end.
  (* foo1_False'@{α ; u |} : foo1@{α ; u} -> False *)
  (* α ; u |= α -> Prop *)
  About foo1_False'.

  Inductive foo2 := Foo2 : Type -> foo2.
  (* foo2@{α ; u |} : Type@{α ; u+1} *)
  About foo2.
  Fail Check foo2_rect.
  (* The reference foo2_rect was not found in the current environment. Did you mean bool_rect, sig2_rect, prod_rect, ex2_rect or bool_rec? *)

  Inductive foo3 A := Foo3 : A -> foo3 A.
  (* foo3@{α α0 ; u |} (A : Type@{α0 ; u}) : Type@{α ; u} *)
  About foo3.
  Fail Check foo3_rect.
  (* The reference foo3_rect was not found in the current environment. Did you mean bool_rect, prod_rect or bool_rec? *)

  Inductive foo5 (A : Type) : Prop := Foo5 (_ : A).
  (* foo5@{α ; u} : Type@{α ; u} -> Prop *)
  About foo5.

  Definition foo5_ind' : forall (A : Type) (P : Prop), (A -> P) -> foo5 A -> P
    := foo5_ind.
  About foo5_ind'.

  Definition foo5_Prop_rect (A:Prop) (P:foo5 A -> Type)
    (H : forall a, P (Foo5 A a))
    (f : foo5 A)
    : P f
    := match f with Foo5 _ a => H a end.
  (* foo5_Prop_rect@{α ; u} :
    forall (A : Prop) (P : foo5@{Type ; Set} A -> Type@{α ; u}),
    (forall a : A, P (Foo5@{Type ; Set} A a)) -> forall f : foo5@{Type ; Set} A, P f *)
  (* α ; u |= Prop -> α *)
  About foo5_Prop_rect.

  Definition foo5_Prop_rect' (A : Prop) (P : foo5 A -> Type)
    (H : forall a, P (Foo5 A a))
    (f : foo5@{Prop;_} A)
    : P f
    := match f with Foo5 _ a => H a end.
  (* foo5_Prop_rect'@{α ; u} :
    forall (A : Prop) (P : foo5@{Prop ; Set} A -> Type@{α ; u}),
    (forall a : A, P (Foo5@{Prop ; Set} A a)) -> forall f : foo5@{Prop ; Set} A, P f *)
  (* α ; u |=  *)
  About foo5_Prop_rect'.

  Inductive foo6 : Type := Foo6.
  About foo6.
  Fail Check foo6_sind.
  (* The reference foo6_sind was not found in the current environment. Did you mean foo5_sind, foo5_ind, bool_sind, prod_sind, or_sind, foo5_ind' or bool_ind? *)

  Definition foo6_rect (P:foo6 -> Type)
    (H : P Foo6)
    (f : foo6)
    : P f
    := match f with Foo6 => H end.
  (* foo6_rect@{α α0 ; u u0} : forall P : foo6@{α0 ; u} -> Type@{α ; u0}, P Foo6@{α0 ; u} -> forall f : foo6@{α0 ; u}, P f *)
  (* α α0 ; u u0 |= α0 -> α *)
  About foo6_rect.

  Definition foo6_prop_rect (P:foo6 -> Type)
    (H : P Foo6)
    (f : foo6@{Prop;_})
    : P f
    := match f with Foo6 => H end.
  (* foo6_prop_rect@{α ; u u0} : forall P : foo6@{Prop ; u} -> Type@{α ; u0}, P Foo6@{Prop ; u} -> forall f : foo6@{Prop ; u}, P f *)
  (* α ; u u0 |=  *)
  About foo6_prop_rect.

  Definition foo6_type_rect (P:foo6 -> Type)
    (H : P Foo6)
    (f : foo6@{Type;_})
    : P f
    := match f with Foo6 => H end.
  (* foo6_type_rect@{α ; u u0} : forall P : foo6@{Type ; u} -> Type@{α ; u0}, P Foo6@{Type ; u} -> forall f : foo6@{Type ; u}, P f *)
  (* α ; u u0 |=  *)
  About foo6_type_rect.

  Inductive foo7 : Type := Foo7_1 | Foo7_2.
  About foo7.
  Fail Check foo7_sind.
  Fail Check foo7_ind.

  Definition foo7_prop_ind (P:foo7 -> Prop)
    (H : P Foo7_1) (H' : P Foo7_2)
    (f : foo7@{Prop;})
    : P f
    := match f with Foo7_1 => H | Foo7_2 => H' end.
  About foo7_prop_ind.

  Definition foo7_prop_rect (P:foo7 -> Type)
    (H : P Foo7_1) (H' : P Foo7_2)
    (f : foo7@{Prop;})
    : P f
    := match f with Foo7_1 => H | Foo7_2 => H' end.
  About foo7_prop_rect.

  (*********************************************)
  (*                 SIGMA                     *)
  (*********************************************)
  Inductive sigma (A:Type) (B:A -> Type) : Type
    := pair : forall x : A, B x -> sigma A B.
  (* Inductive sigma@{α α0 α1 ; u u0 |} (A : Type@{α ; u}) (B : A -> Type@{α0 ; u0}) : Type@{α1 ; max(u,u0)} *)
  About sigma.

  Definition sigma_srect A B
    (P : sigma A B -> Type)
    (H : forall x b, P (pair _ _ x b))
    (s:sigma A B)
    : P s
    := match s with pair _ _ x b => H x b end.
  (* α α0 α1 α2 ; u u0 u1 |= α2 -> α *)
  About sigma_srect.

  (* Elimination constraints are added *)
  Definition pr1 {A B} (s:sigma A B) : A
    := match s with pair _ _ x _ => x end.
  (* α α0 α1 ; u u0 |= α1 -> α *)
  About pr1.

  Definition pr2 {A B} (s:sigma A B) : B (pr1 s)
    := match s with pair _ _ _ y => y end.
  (* α α0 α1 ; u u0 |= α1 -> α
                       α1 -> α0 *)
  About pr2.


  Definition π1 {A:Type} {P:A -> Type} (p : sigma@{Type _ _;_ _} A P) : A :=
    match p return A with pair _ _ a _ => a end.
  (* α α0 ; u u0 |= α0 -> Type *)
  About π2.

  (*********************************************)
  (*                   EQ                      *)
  (*********************************************)
  Inductive seq (A:Type) (a:A) : A -> Prop := seq_refl : seq A a a.
  (* Inductive seq@{α ; u |} (A : Type@{α ; u}) (a : A) : A -> Prop *)
  Arguments seq_refl {_ _}.
  About seq.

  Definition eta A B (s:sigma A B) : seq _ s (pair A B (pr1 s) (pr2 s)).
  Proof.
    destruct s. simpl. reflexivity.
  Qed.
  About eta.

  (*********************************************)
  (*                   SUM                     *)
  (*********************************************)
  Inductive sum (A B : Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.
  (* sum@{α α0 α1 ; u u0} : Type@{α ; u} -> Type@{α0 ; u0} -> Type@{α1 ; max(Set,u,u0)} *)
  (* α α0 α1 ; u u0 |=  *)
  About sum.

  Arguments inl {A B} _ , [A] B _.
  Arguments inr {A B} _ , A [B] _.

  (* Elimination constraint left explicitly empty. Definition fails because of missing constraint. *)
  Fail Definition sum_elim@{sl sr s0 s0';ul ur v|}
    (A : Type@{sl;ul}) (B : Type@{sr;ur}) (P : sum@{sl sr s0;ul ur} A B -> Type@{s0';v})
    (fl : forall a, P (inl a)) (fr : forall b, P (inr b)) (x : sum@{sl sr s0;ul ur} A B) :=
    match x with
    | inl a => fl a
    | inr b => fr b
    end.
  (* The command has indeed failed with message:
  Elimination constraints are not implied by the ones declared: s0->s0' *)

  (* Leaving them implicit *)
  Definition sum_elim (A B : Type) (P : sum A B -> Type)
    (fl : forall a, P (inl a)) (fr : forall b, P (inr b)) (x : sum A B) :=
    match x with
    | inl a => fl a
    | inr b => fr b
    end.
  (* α α0 α1 α2 ; u u0 u1 |= α2 -> α *)
  About sum_elim.

  Definition sum_sind := sum_elim@{Type Type Type SProp;_ _ _}.
  Definition sum_rect := sum_elim@{Type Type Type Type;_ _ _}.
  Definition sum_ind := sum_elim@{Type Type Type Prop;_ _ _}.

  Definition or_ind := sum_elim@{Prop Prop Prop Prop;_ _ _}.
  Definition or_sind := sum_elim@{Prop Prop Prop SProp;_ _ _}.
  Fail Definition or_rect := sum_elim@{Prop Prop Prop Type;_ _ _}.
  (* The command has indeed failed with message:
  The quality constraints are inconsistent: cannot enforce Prop -> Type because it would identify Type and Prop which is inconsistent.
  This is introduced by the constraints Prop -> Type *)

  Definition sumor := sum@{Type Prop Type;_ _}.

  Definition sumor_sind := sum_elim@{Type Prop Type SProp;_ _ _}.
  Definition sumor_rect := sum_elim@{Type Prop Type Type;_ _ _}.
  Definition sumor_ind := sum_elim@{Type Prop Type Prop;_ _ _}.

  (* Implicit qualities and constraints are elaborated *)
  Definition idT (A B : Type) (x : sum A B)
    : sum@{_ _ Type; _ _} A B :=
    match x with
    | inl a => inl a
    | inr b => inr b
    end.
  (* α α0 α1 ; u u0 |= α -> Type *)
  About idT.

  (* Implicit qualities and constraints are elaborated *)
  Definition idP (A B : Type) (x : sum A B)
    : sum@{_ _ Prop; _ _} A B :=
    match x with
    | inl a => inl a
    | inr b => inr b
    end.
  (* α α0 α1 ; u u0 |= α -> Prop *)
  About idP.

  (* Implicit qualities and constraints are elaborated *)
  Definition idS (A B : Type) (x : sum A B)
    : sum@{_ _ SProp; _ _} A B :=
    match x with
    | inl a => inl a
    | inr b => inr b
    end.
  (* α α0 α1 ; u u0 |= α -> Prop *)
  About idS.

  (* Implicit qualities and constraints are elaborated *)
  Definition idV (A B : Type) (x : sum A B)
    : sum A B :=
    match x with
    | inl a => inl a
    | inr b => inr b
    end.
  (* α α0 α1 α2 ; u u0 |= α -> α2 *)
  About idV.

  Fail Compute idV@{Prop Type Prop Type;Set Set} (inl I).

  (*********************************************)
  (*                  LIST                     *)
  (*********************************************)
  Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.
  About list.

  Arguments nil {A}.
  Arguments cons {A} _ _.

  Definition list_elim
    (A : Type) (P : list A -> Type)
    (fn : P nil) (fc : forall (x : A) (l : list A), P l -> P (cons x l)) :=
    fix F (l : list A) : P l :=
      match l with
      | nil => fn
      | cons x l => fc x l (F l)
      end.
  (* α α0 α1 ; u u0 |= α1 -> α *)
  About list_elim.

  Fixpoint list_idT {A : Type} (l : list A) : list@{_ Type;_} A :=
    match l with
    | nil => nil
    | cons x l => cons x (list_idT l)
    end.
  (* α α0 ; u |= α -> Type *)
  About list_idT.

  Fixpoint list_idP {A : Type} (l : list A) : list@{_ Prop;_} A :=
    match l with
    | nil => nil
    | cons x l => cons x (list_idP l)
    end.
  (* α α0 ; u |= α -> Prop *)
  About list_idP.

  Fixpoint list_idS {A : Type} (l : list A) : list@{_ SProp;_} A :=
    match l with
    | nil => nil
    | cons x l => cons x (list_idS l)
    end.
  (* α α0 ; u |= α -> SProp *)
  About list_idS.

  Fixpoint map A B f (l : list A) : list B :=
    match l with
    | nil => nil
    | cons x l' => cons (f x) (map A B f l')
    end.
  (* map@{α α0 α1 α2 ; u u0} :
      forall (A : Type@{α ; u}) (B : Type@{α1 ; u0}) (_ : forall _ : A, B)
      (_ : list@{α α0 ; u} A), list@{α1 α2 ; u0} B *)
  (* α α0 α1 α2 ; u u0 |= α0 -> α2 *)
  About map.

  (*********************************************)
  (*                  FALSE                    *)
  (*********************************************)
  Inductive False' : Type :=.
  (* False'@{α ; u} : Type@{α ; u} *)
  About False'.

  Definition False'_False (x : False') : False := match x return False with end.
  (* α ; u |= α -> Prop *)
  About False'_False.

  (*********************************************)
  (*                  BOOL                     *)
  (*********************************************)
  Inductive bool : Type := true | false.
  About bool.

  Definition bool_to_Prop (b : bool) : Prop.
  Proof.
    destruct b.
    - exact True.
    - exact False.
  Defined.
  (* α ;  |= α -> Type *)
  About bool_to_Prop.

  Definition bool_to_True_conj (b : bool) : True \/ True.
  Proof.
    destruct b.
    - exact (or_introl I).
    - exact (or_intror I).
  Defined.
  (* α ;  |= α -> Prop *)
  About bool_to_True_conj.

  (* Using Program *)
  Program Definition bool_to_Prop' (b : bool) : Prop := _.
  Next Obligation.
    intro b; destruct b.
    - exact True.
    - exact False.
  Defined.
  (* α ;  |= α -> Type *)
  About bool_to_Prop'.

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
  Inductive unit : Type := tt.
  (* unit@{α ; u} : Type@{α ; u} *)
  About unit.

  (*********************************************)
  (*                  MISC                     *)
  (*********************************************)
  (* Interactive definition *)
  Inductive FooNat :=
  | FO : FooNat
  | FS : FooNat -> FooNat.
  About FooNat.

  Definition Foo (n : FooNat) : FooNat.
    destruct n.
    - exact FO.
    - exact FO.
  Defined.
  About Foo.

  Check Foo@{Type Prop;}.
  Fail Check Foo@{Prop Type;}.
End Inductives.

Module Records.

  Set Primitive Projections.
  Set Warnings "+records".

  (* the SProp instantiation may not be primitive so the whole thing must be nonprimitive *)
  Fail Record R1 : Type := {}.

  Record R2 (A:SProp) : Type := { R2f1 : A }.
  (* R2@{α ; u} : SProp -> Type@{α ; _} *)
  About R2.

  Record R3 (A:Type) : Type := { R3f1 : A }.
  (* R3@{α α0 ; u} : forall _ : Type@{α ; u}, Type@{α0 ; u} *)
  (* α α0 ; u |= α0 -> α *)
  About R3.

  Record R4@{s; |} (A:Type@{s;Set}) : Type@{s;Set} := { R4f1 : A}.
  About R4.

  (* non SProp instantiation must be squashed *)
  Fail Record R5 (A:Type) : SProp := { R5f1 : A}.
  #[warnings="-non-primitive-record"]
    Record R5 (A:Type) : SProp := { R5f1 : A}.
  (* R5@{α ; u} : forall _ : Type@{α ; u}, SProp *)
  (* α ; u |= SProp -> α *)
  About R5.

  Record R6@{s; |+} (A:Type@{s;Set}) : Set := { R6f1 : A; R6f2 : nat }.
  About R6.

  Check fun (A:SProp) (x y : R6 A) =>
          eq_refl : Conversion.box _ x.(R6f1 _) = Conversion.box _ y.(R6f1 _).
  Fail Check fun (A:Prop) (x y : R6 A) =>
          eq_refl : Conversion.box _ x.(R6f1 _) = Conversion.box _ y.(R6f1 _).
  Fail Check fun (A:SProp) (x y : R6 A) =>
          eq_refl : Conversion.box _ x.(R6f2 _) = Conversion.box _ y.(R6f2 _).

  (* Elimination constraints are added specifically for each projection *)
  #[projections(primitive=no)] Record R7 (A:Type) := { R7f1 : A; R7f2 : nat }.
  (* Record R7@{α α0 ; u |} (A : Type@{α ; u}) : Type@{α0 ; max(Set,u)}  *)
  (* R7f1@{α α0 ; u |} : forall A : Type@{α ; u}, R7@{α α0 ; u} A -> A
      α α0 ; u |= α0 -> α *)
  (* R7f2@{α α0 ; u |} : forall A : Type@{α ; u}, R7@{α α0 ; u} A -> nat
      α α0 ; u |= α0 -> Type *)
  About R7.
  About R7f1.
  About R7f2.

  (* sigma as a primitive record works better *)
  Record Rsigma@{s;u v|} (A:Type@{s;u}) (B:A -> Type@{s;v}) : Type@{s;max(u,v)}
    := Rpair { Rpr1 : A; Rpr2 : B Rpr1 }.
  About Rsigma.

  (* match desugared to primitive projections using definitional eta *)
  Definition Rsigma_srect A B
    (P : Rsigma A B -> Type)
    (H : forall x b, P (Rpair _ _ x b))
    (s:Rsigma A B)
    : P s
    := match s with Rpair _ _ x b => H x b end.
  (* Rsigma_srect@{α α0 ; u u0 u1 |} : forall (A : Type@{α0 ; _}) (B : A -> Type@{α0 ; _})
         (P : Rsigma A B -> Type@{α ; _}),
       (forall (x : A) (b : B x), P {| Rpr1 := x; Rpr2 := b |}) ->
       forall s : Rsigma A B, P s *)
  About Rsigma_srect.

  (* sort polymorphic exists (we could also make B sort poly)
     can't be a primitive record since the first projection isn't defined at all sorts *)
  Inductive sexists (A:Type) (B:A -> Prop) : Prop
    := sexist : forall a:A, B a -> sexists A B.
  About sexists.

  (* we can eliminate to Prop *)
  Check sexists_ind.

  Unset Primitive Projections.

  (* Elimination constraints are added specifically for each projection *)
  Record R8 := {
    R8f1 : Type;
    R8f2 : R8f1
  }.
  (* Record R8@{α α0 ; u |} : Type@{α ; u+1}. *)
  (* R8f1@{α α0 ; u |} : R8@{α α0 ; u} -> Type@{α0 ; u}
      α α0 ; u |= α -> Type *)
  (* R8f2@{α α0 ; u |} : forall r : R8@{α α0 ; u}, R8f1@{α α0 ; u} r
      α α0 ; u |= α -> α0
                  α -> Type *)
  About R8.
  About R8f1.
  About R8f2.

  Inductive eq {A} x : A -> Type :=
  eq_refl : eq x x.

  Inductive bool := true | false.

  (* Elimination constraints are added specifically for each projection *)
  Record R9 := {
    R9f1 : bool ;
    R9f2 : bool ;
  }.
  (* R9@{α α0 α1 ; } : Type@{α ; Set} *)
  (* R9f1@{α α0 α1 ; } : forall _ : R9@{α α0 α1 ; }, bool@{α0 ; } *)
        (* α α0 α1 ;  |= α -> α0 *)
  (* R9f2@{α α0 α1 ; } : forall _ : R9@{α α0 α1 ; }, bool@{α1 ; } *)
        (* α α0 α1 ;  |= α -> α1 *)
  About R9.
  About R9f1.
  About R9f2.

  (* Elimination constraints are added specifically for each projection *)
  Record R10 (A : Type) := {
    R10f1 : A ;
    R10f2 : eq R10f1 R10f1 ;
    R10f3 : bool
  }.
  (* R10@{α α0 α1 α2 ; u u0} : forall _ : Type@{α0 ; u}, Type@{α ; max(Set,u,u0)} *)
  (* R10f1@{α α0 α1 α2 ; u u0} : forall (A : Type@{α0 ; u}) (_ : R@{α α0 α1 α2 ; u u0} A), A *)
     (* α α0 α1 α2 ; u u0 |= α -> α0 *)
  (* R10f2@{α α0 α1 α2 ; u u0} : forall (A : Type@{α0 ; u}) (r : R@{α α0 α1 α2 ; u u0} A),
                              @eq@{α0 α1 ; u u0} A (x@{α α0 α1 α2 ; u u0} A r) (x@{α α0 α1 α2 ; u u0} A r) *)
     (* α α0 α1 α2 ; u u0 |= α -> α0
                             α -> α1 *)
  (* R10f3@{α α0 α1 α2 ; u u0} : forall (A : Type@{α0 ; u}) (_ : R@{α α0 α1 α2 ; u u0} A), bool@{α2 ; } *)
     (* α α0 α1 α2 ; u u0 |= α -> α2 *)
  About R10.
  About R10f1.
  About R10f2.
  About R10f3.

  Record R11 := {
    R11f1 : bool ;
    R11f2 : let r := {| R10f1 := true; R10f2 := eq_refl true ; R10f3 := R11f1 |} in
         if R10f3 bool r then
          bool
        else
          bool ;
    R11f3 : bool
  }.
  (* R11@{α α0 α1 α2 α3 α4 α5 ; u} : Type@{α ; Set} *)
       (* α α0 α1 α2 α3 α4 α5 ; u |= α0 -> α3
                                     α3 -> Type *)
  (* R11f2 : ... *)
    (* α α0 α1 α2 α3 α4 α5 ; u |= α -> α3
                              α -> α4
                              α0 -> α3
                              α3 -> Type *)
  (* R11f3 : ... *)
    (* α α0 α1 α2 α3 α4 α5 ; u |= α -> α5
                              α0 -> α3
                              α3 -> Type *)
  About R11.
  About R11f1.
  About R11f2.
  About R11f3.

  Record R12 := {
    R12f1 : bool ;
    R12f2 : let f' :=
          fix F n :=
            if R12f1 then n else O
        in
        match f' O with
        | O => bool
        | S _ => nat
        end
        }.
  About R12.
  About R12f1.
  About R12f2.

 (* Elimination constraints added to the inductive itself and propagated to projections.
    Elimination constraints of projections are specifically for each projection *)
  Record R13 := {
    R13f1 : Type ;
    R13f2 : Type ;
    R13f3 : bool;
    R13f4 : forall (b : bool),
          match b with
          | true => match R13f3 with (* Depends on R13f3 *)
                    | true => R13f1
                    | false => R13f2
                    end
          | false => bool
          end
    }.
   (* R13@{α α0 α1 α2 ; u u0} : Type@{α ; max(Set,u+1,u0+1)} *)
       (* α α0 α1 α2 ; u u0 |= α1 -> Type
                               α2 -> Type,
                               u0 <= u *)
  (* R13f3@{α α0 α1 α2 ; u u0} : forall _ : R'@{α α0 α1 α2 ; u u0}, bool@{α1 ; }  *)
      (* α α0 α1 α2 ; u u0 |= α -> α1
                              α1 -> Type
                              α2 -> Type,
                              u0 <= u *)
  (* R13f4@{α α0 α1 α2 ; u u0} : ... *)
      (* α α0 α1 α2 ; u u0 |= α -> α0
                              α -> α1
                              α -> Type
                              α1 -> Type
                              α2 -> Type,
                              u0 <= u *)
  About R13.
  About R13f1.
  About R13f2.
  About R13f3.
  About R13f4.

End Records.

Module Classes.

  Class C1 (A : Type) : Type := {
    C1f1 : A
  }.
  About C1.
  About C1f1.

  Inductive unit : Type := tt.

  Instance C1I1 : C1 unit := { C1f1 := tt }.
  About C1I1.

  Program Instance C1ProgramI1 : C1 unit.
  Next Obligation.
    exact tt.
  Defined.
  About C1ProgramI1.

  #[refine]
  Instance C1RefineI1 : C1 unit := { C1f1 := _ }.
  exact tt.
  Defined.
  About C1RefineI1.

  Instance C1InteractiveI1 : C1 unit.
  Proof. constructor. exact tt. Defined.
  About C1InteractiveI1.

  Axiom (C1AxiomaticI1 : C1 unit).
  Existing Instance C1AxiomaticI1.
  About C1AxiomaticI1.

  Inductive C1InductiveI1 := mkInductive.
  About C1InductiveI1.

  Existing Class C1InductiveI1.

End Classes.

Unset Universe Polymorphism.
Set Collapse Sorts ToType.
Fail #[universes(collapse_sort_variables=no)]
Inductive Attr : Type := attr.

#[universes(polymorphic, collapse_sort_variables=no)]
Inductive Attr : Type := attr.
About Attr.
