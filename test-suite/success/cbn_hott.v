(* -*- mode: coq; coq-prog-args: ("-emacs" "-noinit" "-indices-matter") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 451 lines to 58 lines, then from 72 lines to 1063 lines, then from 1070 lines to 273 lines, then from 287 lines to 1386 lines, then from 1393 lines to 535 lines, then from 549 lines to 1150 lines, then from 1157 lines to 601 lines, then from 615 lines to 1562 lines, then from 1569 lines to 686 lines, then from 700 lines to 1504 lines, then from 1511 lines to 725 lines, then from 739 lines to 1253 lines, then from 1260 lines to 803 lines, then from 817 lines to 870 lines, then from 877 lines to 812 lines, then from 826 lines to 1201 lines, then from 1208 lines to 864 lines, then from 878 lines to 1089 lines, then from 1096 lines to 921 lines, then from 935 lines to 2032 lines, then from 2039 lines to 946 lines, then from 960 lines to 1000 lines, then from 1007 lines to 952 lines, then from 966 lines to 1021 lines, then from 1028 lines to 983 lines, then from 997 lines to 1238 lines, then from 1245 lines to 1119 lines, then from 1133 lines to 1532 lines, then from 1538 lines to 1275 lines, then from 1289 lines to 1477 lines, then from 1484 lines to 1319 lines, then from 1333 lines to 1447 lines, then from 1454 lines to 1395 lines, then from 1406 lines to 2147 lines, then from 2154 lines to 1554 lines, then from 1565 lines to 2417 lines, then from 2422 lines to 1574 lines, then from 1585 lines to 2475 lines, then from 2481 lines to 1639 lines, then from 1650 lines to 2389 lines, then from 2395 lines to 1776 lines, then from 1787 lines to 3348 lines, then from 3354 lines to 1827 lines, then from 1838 lines to 2550 lines, then from 2554 lines to 1919 lines, then from 1930 lines to 2744 lines, then from 2750 lines to 2076 lines, then from 2087 lines to 2402 lines, then from 2406 lines to 2114 lines, then from 2124 lines to 2222 lines, then from 2228 lines to 2136 lines, then from 2142 lines to 2137 lines, then from 2143 lines to 1766 lines, then from 1772 lines to 1766 lines, then from 0 lines to 1766 lines *)
(* coqc version 9.3+alpha compiled with OCaml 5.4.0
   coqtop version 9.3+alpha
   Expected coqc runtime on this file: 0.000 sec
   Expected coqc peak memory usage on this file: 0.0 kb *)

Require Corelib.Init.Ltac.

Inductive False : Prop := .
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.

Declare ML Module "rocq-runtime.plugins.ltac".

Global Set Default Proof Mode "Classic".

Global Set Universe Polymorphism.

Global Unset Strict Universe Declaration.

Global Set Primitive Projections.
Create HintDb typeclass_instances discriminated.
Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Reserved Notation "~ x" (at level 35, right associativity).

Reserved Notation "x = y  :>  T"
(at level 70, y at next level, no associativity).

Reserved Notation "x + y" (at level 50, left associativity).
Reserved Notation "x * y" (at level 40, left associativity).

Reserved Notation "{ x : A  & P }" (at level 0, x at level 99).
Reserved Notation "p @ q" (at level 20).
Reserved Notation "p # x" (right associativity, at level 65).
Reserved Notation "p @@ q" (at level 20).
Reserved Notation "f == g" (at level 70, no associativity).

Reserved Notation "A <~> B" (at level 85).

Reserved Infix "$->" (at level 99).
Reserved Infix "$<~>" (at level 85).
Reserved Infix "$o" (at level 40, left associativity).
Reserved Infix "$==" (at level 70).
Reserved Infix "$@" (at level 30).
Reserved Infix "$@L" (at level 30).
Reserved Infix "$@R" (at level 30).
Reserved Infix "$=>" (at level 99).
Reserved Notation "g 'o' f" (at level 40, left associativity).

Declare Scope core_scope.
Declare Scope fibration_scope.
Delimit Scope function_scope with function.
Delimit Scope type_scope with type.
Delimit Scope path_scope with path.
Global Open Scope path_scope.
Global Open Scope fibration_scope.
Global Open Scope function_scope.
Global Open Scope type_scope.
Global Open Scope core_scope.
Module Export Overture.

Local Unset Elimination Schemes.

Notation "A -> B" := (forall (_ : A), B) : type_scope.

Inductive sum (A B : Type) : Type :=
| inl : A -> sum A B
| inr : B -> sum A B.
Scheme sum_ind := Induction for sum Sort Type.
Arguments sum_ind {A B} P f g : rename.

Notation "x + y" := (sum x y) : type_scope.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

Record prod (A B : Type) := pair { fst : A ; snd : B }.

Arguments pair {A B} _ _.
Arguments fst {A B} _ / .
Arguments snd {A B} _ / .

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

#[export] Hint Resolve pair inl inr : core.

Local Set Typeclasses Strict Resolution.

Definition Relation (A : Type) := A -> A -> Type.

Class Reflexive {A} (R : Relation A) :=
  reflexivity : forall x : A, R x x.

Class Transitive {A} (R : Relation A) :=
  transitivity : forall x y z, R x y -> R y z -> R x z.

Ltac old_reflexivity := reflexivity.
Tactic Notation "reflexivity" :=
  old_reflexivity
|| (intros;
  let R := match goal with |- ?R ?x ?y => constr:(R) end in
  let pre_proof_term_head := constr:(@reflexivity _ R _) in
  let proof_term_head := (eval cbn in pre_proof_term_head) in
  apply (proof_term_head : forall x, R x x)).

Tactic Notation "etransitivity" open_constr(y) :=
  let R := match goal with |- ?R ?x ?z => constr:(R) end in
  let x := match goal with |- ?R ?x ?z => constr:(x) end in
  let z := match goal with |- ?R ?x ?z => constr:(z) end in
  let pre_proof_term_head := constr:(@transitivity _ R _) in
  let proof_term_head := (eval cbn in pre_proof_term_head) in
  refine (proof_term_head x y z _ _); [ change (R x y) | change (R y z) ].

Tactic Notation "etransitivity" := etransitivity _.

Notation Type0 := Set.

Record sig {A} (P : A -> Type) := exist {
  proj1 : A ;
  proj2 : P proj1 ;
}.

Arguments exist {A}%_type P%_type _ _.
Notation "{ x : A  & P }" := (sig (fun x:A => P)) : type_scope.

Notation "( x ; y )" := (exist _ x y) : fibration_scope.

Notation idmap := (fun x => x).

Notation compose := (fun g f x => g (f x)).

Notation "g 'o' f" := (compose g%function f%function) : function_scope.

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Scheme paths_ind := Induction for paths Sort Type.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.
Definition inverse {A : Type} {x y : A} (p : x = y) : y = x.
exact (match p with idpath => idpath end).
Defined.

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with idpath, idpath => idpath end.

Notation "1" := idpath : path_scope.

Notation "p @ q" := (concat p%path q%path) : path_scope.

Notation "p ^" := (inverse p%path) : path_scope.
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y.
Admitted.

Notation "p # u" := (transport _ p u) (only parsing) : path_scope.
Definition ap {A B : Type} (f : A -> B) {x y : A} (p : x = y) : f x = f y.
exact (match p with idpath => idpath end).
Defined.
Definition apD {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} (p:x=y):
  p # (f x) = f y.
Admitted.

Definition pointwise_paths A (P : A -> Type) (f g : forall x, P x)
  := forall x, f x = g x.

Instance transitive_pointwise_paths A P
  : Transitive (pointwise_paths A P).
Admitted.

Global Arguments pointwise_paths {A}%_type_scope {P} (f g)%_function_scope.

Notation "f == g" := (pointwise_paths f g) : type_scope.

Class IsEquiv {A B : Type} (f : A -> B) := {
  equiv_inv : B -> A ;
  eisretr : f o equiv_inv == idmap ;
  eissect : equiv_inv o f == idmap ;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x) ;
}.

Arguments eisretr {A B}%_type_scope f%_function_scope {_} _.
Arguments eissect {A B}%_type_scope f%_function_scope {_} _.

Record Equiv A B := {
  equiv_fun : A -> B ;
  equiv_isequiv :: IsEquiv equiv_fun
}.

Coercion equiv_fun : Equiv >-> Funclass.

Notation "A <~> B" := (Equiv A B) : type_scope.

Notation "f ^-1" := (@equiv_inv _ _ f _) : function_scope.

Inductive Empty : Type0 := .

Definition not (A : Type) := A -> Empty.
Notation "~ x" := (not x) : type_scope.

End Overture.

Tactic Notation "do_with_holes" tactic3(x) uconstr(p) :=
  x uconstr:(p) ||
  x uconstr:(p _) ||
  x uconstr:(p _ _) ||
  x uconstr:(p _ _ _) ||
  x uconstr:(p _ _ _ _) ||
  x uconstr:(p _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Class IsGlobalAxiom (A : Type) : Type0 := {}.

Ltac is_global_axiom A := let _ := constr:(_ : IsGlobalAxiom A) in idtac.

Ltac global_axiom := try match goal with
    | |- ?G  => is_global_axiom G; exact _
end.

Tactic Notation "srefine" uconstr(term) := simple refine term.

Tactic Notation "nrefine" uconstr(term) := notypeclasses refine term; global_axiom.

Tactic Notation "snrefine" uconstr(term) := simple notypeclasses refine term; global_axiom.

Tactic Notation "napply" uconstr(term)
  := do_with_holes ltac:(fun x => nrefine x) term.

Tactic Notation "rapply" uconstr(term)
  := do_with_holes ltac:(fun x => assert_succeeds (nrefine x); refine x) term.

Tactic Notation "tapply" uconstr(term)
  := do_with_holes ltac:(fun x => refine x) term.

Tactic Notation "snapply" uconstr(term)
  := do_with_holes ltac:(fun x => snrefine x) term.

Tactic Notation "srapply" uconstr(term)
  := do_with_holes ltac:(fun x => assert_succeeds (simple notypeclasses refine x); srefine x) term.

Tactic Notation "lhs" tactic3(tac) := nrefine (ltac:(tac) @ _).

Ltac done :=
  trivial; intros; solve
    [ repeat first
      [ solve [trivial]
      | solve [symmetry; trivial]
      | reflexivity

      | contradiction
      | split ]
    | match goal with
      H : ~ _ |- _ => solve [destruct H; trivial]
      end ].

Tactic Notation "by" tactic(tac) :=
  tac; done.
Definition concat_p_pp {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p @ (q @ r) = (p @ q) @ r.
Admitted.
Definition concat_pp_p {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  (p @ q) @ r = p @ (q @ r).
Admitted.
Definition concat_V_pp {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  p^ @ (p @ q) = q.
Admitted.

Definition moveR_pV {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x) :
  r = q @ p -> r @ p^ = q.
Admitted.
Definition ap_V {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
  ap f (p^) = (ap f p)^.
Admitted.

Definition transport_const {A B : Type} {x1 x2 : A} (p : x1 = x2) (y : B)
  : transport (fun x => B) p y = y.
Admitted.

Lemma apD_const {A B} {x y : A} (f : A -> B) (p: x = y) :
  apD f p = transport_const p (f x) @ ap f p.
Admitted.
Definition concat2 {A} {x y z : A} {p p' : x = y} {q q' : y = z} (h : p = p') (h' : q = q')
  : p @ q = p' @ q'.
Admitted.

Notation "p @@ q" := (concat2 p q)%path : path_scope.
Definition whiskerL {A : Type} {x y z : A} (p : x = y)
  {q r : y = z} (h : q = r) : p @ q = p @ r.
Admitted.
Definition whiskerR {A : Type} {x y z : A} {p q : x = y}
  (h : p = q) (r : y = z) : p @ r = q @ r.
Admitted.
Definition cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
: (p @ q = p @ r) -> (q = r).
exact (fun h => (concat_V_pp p q)^ @ whiskerL p^ h @ (concat_V_pp p r)).
Defined.

Class IsGraph (A : Type) :=
{
  Hom : A -> A -> Type
}.

Notation "a $-> b" := (Hom a b).

Class Is01Cat (A : Type) `{IsGraph A} :=
{
  Id  : forall (a : A), a $-> a;
  cat_comp : forall (a b c : A), (b $-> c) -> (a $-> b) -> (a $-> c);
}.
Arguments cat_comp {A _ _ a b c} _ _.
Notation "g $o f" := (cat_comp g f).
Definition cat_postcomp {A} `{Is01Cat A} (a : A) {b c : A} (g : b $-> c)
  : (a $-> b) -> (a $-> c).
exact (cat_comp g).
Defined.
Definition cat_precomp {A} `{Is01Cat A} {a b : A} (c : A) (f : a $-> b)
  : (b $-> c) -> (a $-> c).
Admitted.

Class Is0Gpd (A : Type) `{Is01Cat A} :=
  { gpd_rev : forall {a b : A}, (a $-> b) -> (b $-> a) }.

Definition GpdHom {A} `{Is0Gpd A} (a b : A) := a $-> b.
Notation "a $== b" := (GpdHom a b).
Instance reflexive_GpdHom {A} `{Is0Gpd A}
  : Reflexive GpdHom.
Admitted.
Definition gpd_comp {A} `{Is0Gpd A} {a b c : A}
  : (a $== b) -> (b $== c) -> (a $== c).
Admitted.
Infix "$@" := gpd_comp.

Notation "p ^$" := (gpd_rev p).

Class Is0Functor {A B : Type} `{IsGraph A} `{IsGraph B} (F : A -> B)
  := { fmap : forall (a b : A) (f : a $-> b), F a $-> F b }.

Arguments Build_Is0Functor {A B isgraph_A isgraph_B} F fmap : rename.
Arguments fmap {A B isgraph_A isgraph_B} F {is0functor_F a b} f : rename.

Class Is2Graph (A : Type) `{IsGraph A}
  := isgraph_hom : forall (a b : A), IsGraph (a $-> b).
Existing Instance isgraph_hom | 20.

Class Is1Cat (A : Type) `{!IsGraph A, !Is2Graph A, !Is01Cat A} :=
{
  is01cat_hom :: forall (a b : A), Is01Cat (a $-> b) ;
  is0gpd_hom :: forall (a b : A), Is0Gpd (a $-> b) ;
  is0functor_postcomp :: forall (a b c : A) (g : b $-> c), Is0Functor (cat_postcomp a g) ;
  is0functor_precomp :: forall (a b c : A) (f : a $-> b), Is0Functor (cat_precomp c f) ;
  cat_assoc : forall (a b c d : A) (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f $== h $o (g $o f);
  cat_assoc_opp : forall (a b c d : A) (f : a $-> b) (g : b $-> c) (h : c $-> d),
    h $o (g $o f) $== (h $o g) $o f;
  cat_idl : forall (a b : A) (f : a $-> b), Id b $o f $== f;
  cat_idr : forall (a b : A) (f : a $-> b), f $o Id a $== f;
}.

Arguments cat_assoc {_ _ _ _ _ _ _ _ _} f g h.
Arguments cat_idl {_ _ _ _ _ _ _} f.
Arguments cat_idr {_ _ _ _ _ _ _} f.
Definition cat_postwhisker {A} `{Is1Cat A} {a b c : A}
           {f g : a $-> b} (h : b $-> c) (p : f $== g)
  : h $o f $== h $o g.
Admitted.
Notation "h $@L p" := (cat_postwhisker h p).
Definition cat_prewhisker {A} `{Is1Cat A} {a b c : A}
           {f g : b $-> c} (p : f $== g) (h : a $-> b)
  : f $o h $== g $o h.
Admitted.
Notation "p $@R h" := (cat_prewhisker p h).

Class Is1Cat_Strong (A : Type)`{!IsGraph A, !Is2Graph A, !Is01Cat A} :=
{
  is01cat_hom_strong : forall (a b : A), Is01Cat (a $-> b) ;
  is0gpd_hom_strong : forall (a b : A), Is0Gpd (a $-> b) ;
  is0functor_postcomp_strong : forall (a b c : A) (g : b $-> c),
    Is0Functor (cat_postcomp a g) ;
  is0functor_precomp_strong : forall (a b c : A) (f : a $-> b),
    Is0Functor (cat_precomp c f) ;
  cat_assoc_strong : forall (a b c d : A)
    (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f = h $o (g $o f) ;
  cat_assoc_opp_strong : forall (a b c d : A)
    (f : a $-> b) (g : b $-> c) (h : c $-> d),
    h $o (g $o f) = (h $o g) $o f ;
  cat_idl_strong : forall (a b : A) (f : a $-> b), Id b $o f = f ;
  cat_idr_strong : forall (a b : A) (f : a $-> b), f $o Id a = f ;
}.

Definition is1cat_is1cat_strong (A : Type) `{Is1Cat_Strong A}
  : Is1Cat A.
Admitted.

Hint Immediate is1cat_is1cat_strong : typeclass_instances.

Class Is1Functor {A B : Type} `{Is1Cat A} `{Is1Cat B}
  (F : A -> B) `{!Is0Functor F} :=
{
  fmap2 : forall a b (f g : a $-> b), (f $== g) -> (fmap F f $== fmap F g) ;
  fmap_id : forall a, fmap F (Id a) $== Id (F a);
  fmap_comp : forall a b c (f : a $-> b) (g : b $-> c),
    fmap F (g $o f) $== fmap F g $o fmap F f;
}.

Arguments fmap2 {A B
  isgraph_A is2graph_A is01cat_A is1cat_A
  isgraph_B is2graph_B is01cat_B is1cat_B}
  F {is0functor_F is1functor_F a b f g} p : rename.

  #[export] Instance is0functor_idmap {A : Type} `{IsGraph A} : Is0Functor idmap.
Admitted.

Instance is0functor_compose {A B C : Type}
  `{IsGraph A, IsGraph B, IsGraph C}
  (F : A -> B) `{!Is0Functor F} (G : B -> C) `{!Is0Functor G}
  : Is0Functor (G o F).
Admitted.

Instance isequiv_idmap (A : Type) : IsEquiv idmap | 0 :=
  Build_IsEquiv A A idmap idmap (fun _ => 1) (fun _ => 1) (fun _ => 1).
Definition equiv_idmap (A : Type) : A <~> A.
exact (Build_Equiv A A idmap _).
Defined.

Arguments equiv_idmap {A} , A.

Section Adjointify.

  Context {A B : Type} (f : A -> B) (g : B -> A).
  Context (isretr : f o g == idmap) (issect : g o f == idmap).

  Let issect' := fun x =>
    ap g (ap f (issect x)^)  @  ap g (isretr (f x))  @  issect x.

  Local Definition is_adjoint' (a : A) : isretr (f a) = ap f (issect' a).
Admitted.
Definition isequiv_adjointify : IsEquiv f.
exact (Build_IsEquiv A B f g isretr issect' is_adjoint').
Defined.
Definition equiv_adjointify : A <~> B.
exact (Build_Equiv A B f isequiv_adjointify).
Defined.

End Adjointify.

Definition equiv_homotopic_inverse {A B} (e : A <~> B)
  {f : A -> B} {g : B -> A} (h : f == e) (k : g == e^-1)
  : A <~> B.
Proof.
  snapply equiv_adjointify.
  -
 exact f.
  -
 exact g.
  -
 intro a.
 exact (ap f (k a) @ h _ @ eisretr e a).
  -
 intro b.
 exact (ap g (h b) @ k _ @ eissect e b).
Defined.

Definition transport_paths_Fr {A B : Type} {g : A -> B} {y1 y2 : A} {x : B}
  (p : y1 = y2) (q : x = g y1)
  : transport (fun y => x = g y) p q = q @ (ap g p).
Admitted.
Definition equiv_p1_1q {A : Type} {x y : A} {p q : x = y}
  : p = q <~> p @ 1 = 1 @ q.
Admitted.

Class HasEquivs (A : Type) `{Is1Cat A} :=
{
  CatEquiv' : A -> A -> Type where "a $<~> b" := (CatEquiv' a b);
  CatIsEquiv' : forall a b, (a $-> b) -> Type;
  cate_fun' : forall a b, (a $<~> b) -> (a $-> b);
  cate_isequiv' : forall a b (f : a $<~> b), CatIsEquiv' a b (cate_fun' a b f);
  cate_buildequiv' : forall a b (f : a $-> b), CatIsEquiv' a b f -> CatEquiv' a b;
  cate_buildequiv_fun' : forall a b (f : a $-> b) (fe : CatIsEquiv' a b f),
      cate_fun' a b (cate_buildequiv' a b f fe) $== f;
  cate_inv' : forall a b (f : a $<~> b), b $-> a;
  cate_issect' : forall a b (f : a $<~> b),
    cate_inv' _ _ f $o cate_fun' _ _ f $== Id a;
  cate_isretr' : forall a b (f : a $<~> b),
      cate_fun' _ _ f $o cate_inv' _ _ f $== Id b;
  catie_adjointify' : forall a b (f : a $-> b) (g : b $-> a)
    (r : f $o g $== Id b) (s : g $o f $== Id a), CatIsEquiv' a b f;
}.

Definition CatEquiv {A} `{HasEquivs A} (a b : A)
  := @CatEquiv' A _ _ _ _ _ a b.

Notation "a $<~> b" := (CatEquiv a b).
Definition cate_fun {A} `{HasEquivs A} {a b : A} (f : a $<~> b)
  : a $-> b.
exact (@cate_fun' A _ _ _ _ _ a b f).
Defined.

Coercion cate_fun : CatEquiv >-> Hom.

Class CatIsEquiv {A} `{HasEquivs A} {a b : A} (f : a $-> b)
  := catisequiv : CatIsEquiv' a b f.
Instance cate_isequiv {A} `{HasEquivs A} {a b : A} (f : a $<~> b)
  : CatIsEquiv f.
Admitted.
Definition Build_CatEquiv {A} `{HasEquivs A} {a b : A}
           (f : a $-> b) {fe : CatIsEquiv f}
  : a $<~> b.
exact (cate_buildequiv' a b f fe).
Defined.
Definition cate_buildequiv_fun {A} `{HasEquivs A} {a b : A}
           (f : a $-> b) {fe : CatIsEquiv f}
  : cate_fun (Build_CatEquiv f) $== f.
Admitted.
Definition catie_adjointify {A} `{HasEquivs A} {a b : A}
           (f : a $-> b) (g : b $-> a)
           (r : f $o g $== Id b) (s : g $o f $== Id a)
  : CatIsEquiv f.
exact (catie_adjointify' a b f g r s).
Defined.
Definition cate_adjointify {A} `{HasEquivs A} {a b : A}
           (f : a $-> b) (g : b $-> a)
           (r : f $o g $== Id b) (s : g $o f $== Id a)
  : a $<~> b.
exact (Build_CatEquiv f (fe:=catie_adjointify f g r s)).
Defined.

Definition cate_inv {A} `{HasEquivs A} {a b : A} (f : a $<~> b) : b $<~> a.
Proof.
  simple refine (cate_adjointify _ _ _ _).
  -
 exact (cate_inv' a b f).
  -
 exact f.
  -
 exact (cate_issect' a b f).
  -
 exact (cate_isretr' a b f).
Defined.

Notation "f ^-1$" := (cate_inv f).

Definition cate_issect {A} `{HasEquivs A} {a b : A} (f : a $<~> b)
  : f^-1$ $o f $== Id a.
Admitted.
Definition cate_isretr {A} `{HasEquivs A} {a b : A} (f : a $<~> b)
  : f $o f^-1$ $== Id b.
Admitted.

Definition compose_catie_isretr {A} `{HasEquivs A} {a b c : A}
  (g : b $<~> c) (f : a $<~> b)
  : g $o f $o (f^-1$ $o g^-1$) $== Id c.
Admitted.
Definition compose_catie_issect {A} `{HasEquivs A} {a b c : A}
  (g : b $<~> c) (f : a $<~> b)
  : (f^-1$ $o g^-1$ $o (g $o f) $== Id a).
Admitted.

Instance compose_catie {A} `{HasEquivs A} {a b c : A}
  (g : b $<~> c) (f : a $<~> b)
  : CatIsEquiv (g $o f).
Proof.
  refine (catie_adjointify _ (f^-1$ $o g^-1$) _ _).
  -
 apply compose_catie_isretr.
  -
 apply compose_catie_issect.
Defined.

Class Cat_IsBiInv {A} `{Is1Cat A} {x y : A} (f : x $-> y) := {
  cat_equiv_inv : y $-> x;
  cat_eisretr : f $o cat_equiv_inv $== Id y;
  cat_equiv_inv' : y $-> x;
  cat_eissect' : cat_equiv_inv' $o f $== Id x;
}.

Arguments cat_equiv_inv {A}%_type_scope { _ _ _ _ x y} f {_}.
Arguments cat_eisretr {A}%_type_scope { _ _ _ _ x y} f {_}.

Arguments Build_Cat_IsBiInv {A}%_type_scope {_ _ _ _ x y f} cat_equiv_inv cat_eisretr cat_equiv_inv' cat_eissect'.

Record Cat_BiInv A `{Is1Cat A} (x y : A) := {
  cat_equiv_fun :> x $-> y;
  cat_equiv_isequiv : Cat_IsBiInv cat_equiv_fun;
}.

Existing Instance cat_equiv_isequiv.
Definition cat_eissect {A} `{Is1Cat A} {x y : A} (f : x $-> y) {bif : Cat_IsBiInv f}
  : cat_equiv_inv f $o f $== Id x.
Admitted.

Definition cat_hasequivs A `{Is1Cat A} : HasEquivs A.
Proof.
  srapply Build_HasEquivs; intros x y.
  1: exact (Cat_BiInv _ x y).
  all:intros f; cbn beta in *.
  -
 exact (Cat_IsBiInv f).
  -
 exact f.
  -
 exact _.
  -
 apply Build_Cat_BiInv.
  -
 intros; reflexivity.
  -
 exact (cat_equiv_inv f).
  -
 apply cat_eissect.
  -
 apply cat_eisretr.
  -
 intros g r s.
    exact (Build_Cat_IsBiInv g r g s).
Defined.

Ltac intros_of_type A :=
  repeat match goal with |- forall (a : A), _ => intro a end.

Section Induced_category.
  Context {A B : Type} (f : A -> B).

  Local Instance isgraph_induced `{IsGraph B} : IsGraph A.
  Proof.
    napply Build_IsGraph.
    intros a1 a2.
    exact (f a1 $-> f a2).
  Defined.

  Local Instance is01cat_induced `{Is01Cat B} : Is01Cat A.
  Proof.
    napply Build_Is01Cat; intros_of_type A; cbn.
    +
 apply Id.
    +
 exact cat_comp.
  Defined.

  Local Instance is2graph_induced `{Is2Graph B} : Is2Graph A.
  Proof.
    constructor; cbn.
apply isgraph_hom.
  Defined.

  Local Instance is1cat_induced `{Is1Cat B} : Is1Cat A.
Admitted.

  Definition hasequivs_induced `{HasEquivs B} : HasEquivs A.
  Proof.
    srapply Build_HasEquivs; intros a b; cbn.
    +
 exact (f a $<~> f b).
    +
 apply CatIsEquiv'.
    +
 exact cate_fun.
    +
 apply cate_isequiv'.
    +
 apply cate_buildequiv'.
    +
 napply cate_buildequiv_fun'.
    +
 apply cate_inv'.
    +
 napply cate_issect'.
    +
 napply cate_isretr'.
    +
 napply catie_adjointify'.
  Defined.

End Induced_category.
Definition Square@{u v w} {A : Type@{u}} `{Is1Cat@{u w v} A} {x00 x20 x02 x22 : A}
  (f01 : x00 $-> x02) (f21 : x20 $-> x22) (f10 : x00 $-> x20) (f12 : x02 $-> x22)
  : Type@{w}.
exact (f21 $o f10 $== f12 $o f01).
Defined.

Section Squares.

  Context {A : Type} `{Is1Cat A} {x x' x00 x20 x40 x02 x22 x42 x04 x24 x44 : A}
    {f10 f10' : x00 $-> x20} {f30 : x20 $-> x40}
    {f12 f12' : x02 $-> x22} {f32 : x22 $-> x42}
    {f14 : x04 $-> x24} {f34 : x24 $-> x44}
    {f01 f01' : x00 $-> x02} {f21 f21' : x20 $-> x22} {f41 f41' : x40 $-> x42}
    {f03 : x02 $-> x04} {f23 : x22 $-> x24} {f43 : x42 $-> x44}.
Definition transpose (s : Square f01 f21 f10 f12) : Square f10 f12 f01 f21.
admit.
Defined.

  Definition hinverse {HE : HasEquivs A} (f10 : x00 $<~> x20) (f12 : x02 $<~> x22) (s : Square f01 f21 f10 f12)
    : Square f21 f01 f10^-1$ f12^-1$
    := (cat_idl _)^$ $@ ((cate_issect f12)^$ $@R _) $@ cat_assoc _ _ _
      $@ (_ $@L ((cat_assoc _ _ _)^$ $@ (s^$ $@R _) $@ cat_assoc _ _ _
      $@ (_ $@L cate_isretr f10) $@ cat_idr _)).

End Squares.

Section Squares2.

  Context {A : Type} `{HasEquivs A}
    {x x' x00 x20 x40 x02 x22 x42 x04 x24 x44 : A}
    {f10 f10' : x00 $-> x20} {f30 : x20 $-> x40}
    {f12 f12' : x02 $-> x22} {f32 : x22 $-> x42}
    {f14 : x04 $-> x24} {f34 : x24 $-> x44}
    {f01 f01' : x00 $-> x02} {f21 f21' : x20 $-> x22} {f41 f41' : x40 $-> x42}
    {f03 : x02 $-> x04} {f23 : x22 $-> x24} {f43 : x42 $-> x44}.

  Definition vinverse (f01 : x00 $<~> x02) (f21 : x20 $<~> x22) (s : Square f01 f21 f10 f12)
    : Square (f01^-1$) (f21^-1$) f12 f10
    := transpose (hinverse _ _ (transpose s)).

End Squares2.

Definition Transformation {A : Type} {B : A -> Type} `{forall x, IsGraph (B x)}
  (F G : forall (x : A), B x)
  := forall (a : A), F a $-> G a.

Identity Coercion fun_trans : Transformation >-> Funclass.

Notation "F $=> G" := (Transformation F G).
Definition trans_id {A B : Type} `{Is01Cat B} (F : A -> B)
  : F $=> F.
exact (fun a => Id (F a)).
Defined.
Definition trans_comp {A B : Type} `{Is01Cat B}
           {F G K : A -> B} (gamma : G $=> K) (alpha : F $=> G)
  : F $=> K.
exact (fun a => gamma a $o alpha a).
Defined.

Class Is1Natural {A B : Type} `{IsGraph A, Is1Cat B}
  (F : A -> B) `{!Is0Functor F} (G : A -> B) `{!Is0Functor G}
  (alpha : F $=> G) := Build_Is1Natural' {
  isnat {a a'} (f : a $-> a') : alpha a' $o fmap F f $== fmap G f $o alpha a;

  isnat_tr {a a'} (f : a $-> a') : fmap G f $o alpha a $== alpha a' $o fmap F f;
}.
Arguments isnat {_ _ _ _ _ _ _ _ _ _ _} alpha {alnat _ _} f : rename.
Arguments isnat_tr {_ _ _ _ _ _ _ _ _ _ _} alpha {alnat _ _} f : rename.

Definition Build_Is1Natural {A B : Type} `{IsGraph A} `{Is1Cat B}
  {F G : A -> B} `{!Is0Functor F, !Is0Functor G} (alpha : F $=> G)
  (isnat : forall a a' (f : a $-> a'), alpha a' $o fmap F f $== fmap G f $o alpha a)
  : Is1Natural F G alpha.
Admitted.

Instance is1natural_id {A B : Type} `{IsGraph A} `{Is1Cat B}
  (F : A -> B) `{!Is0Functor F}
  : Is1Natural F F (trans_id F).
Admitted.

Instance is1natural_comp {A B : Type} `{IsGraph A} `{Is1Cat B}
  {F G K : A -> B} `{!Is0Functor F} `{!Is0Functor G} `{!Is0Functor K}
  (gamma : G $=> K) `{!Is1Natural G K gamma}
  (alpha : F $=> G) `{!Is1Natural F G alpha}
  : Is1Natural F K (trans_comp gamma alpha).
Admitted.

Record NatTrans {A B : Type} `{IsGraph A} `{Is1Cat B} {F G : A -> B}
  {ff : Is0Functor F} {fg : Is0Functor G} := {
  #[reversible=no]
  trans_nattrans :> F $=> G;
  is1natural_nattrans :: Is1Natural F G trans_nattrans;
}.

Arguments NatTrans {A B} {isgraph_A}
  {isgraph_B} {is2graph_B} {is01cat_B} {is1cat_B}
  F G {is0functor_F} {is0functor_G} : rename.
Arguments Build_NatTrans {A B isgraph_A isgraph_B is2graph_B is01cat_B is1cat_B
  F G is0functor_F is0functor_G} alpha isnat_alpha : rename.
Definition nattrans_id {A B : Type} (F : A -> B)
  `{IsGraph A, Is1Cat B, !Is0Functor F}
  : NatTrans F F.
exact (Build_NatTrans (trans_id F) _).
Defined.
Definition nattrans_comp {A B : Type} {F G K : A -> B}
  `{IsGraph A, Is1Cat B, !Is0Functor F, !Is0Functor G, !Is0Functor K}
  : NatTrans G K -> NatTrans F G -> NatTrans F K.
exact (fun alpha beta => Build_NatTrans (trans_comp alpha beta) _).
Defined.

Record NatEquiv {A B : Type} `{IsGraph A} `{HasEquivs B}
  {F G : A -> B} `{!Is0Functor F, !Is0Functor G} := {
  #[reversible=no]
  cat_equiv_natequiv :> forall a, F a $<~> G a ;
  is1natural_natequiv :: Is1Natural F G (fun a => cat_equiv_natequiv a) ;
}.

Arguments NatEquiv {A B} {isgraph_A}
  {isgraph_B} {is2graph_B} {is01cat_B} {is1cat_B} {hasequivs_B}
  F G {is0functor_F} {is0functor_G} : rename.

Lemma nattrans_natequiv {A B : Type} `{IsGraph A} `{HasEquivs B}
  {F G : A -> B} `{!Is0Functor F, !Is0Functor G}
  : NatEquiv F G -> NatTrans F G.
Proof.
  intros alpha.
  napply Build_NatTrans.
  exact (is1natural_natequiv alpha).
Defined.
Coercion nattrans_natequiv : NatEquiv >-> NatTrans.

Definition Build_NatEquiv' {A B : Type} `{IsGraph A} `{HasEquivs B}
  {F G : A -> B} `{!Is0Functor F, !Is0Functor G}
  (alpha : NatTrans F G) `{forall a, CatIsEquiv (alpha a)}
  : NatEquiv F G.
Proof.
  snapply Build_NatEquiv.
  -
 intro a.
    exact (Build_CatEquiv (alpha a)).
  -
 snapply Build_Is1Natural'.
    +
 intros a a' f.
      refine ((cate_buildequiv_fun _ $@R _) $@ _ $@ (_ $@L cate_buildequiv_fun _)^$).
      exact (isnat alpha _).
    +
 intros a a' f.
      refine ((_ $@L cate_buildequiv_fun _) $@ _ $@ (cate_buildequiv_fun _ $@R _)^$).
      exact (isnat_tr alpha _).
Defined.
Definition natequiv_compose {A B} {F G H : A -> B} `{IsGraph A} `{HasEquivs B}
  `{!Is0Functor F, !Is0Functor G, !Is0Functor H}
  (alpha : NatEquiv G H) (beta : NatEquiv F G)
  : NatEquiv F H.
exact (Build_NatEquiv' (nattrans_comp alpha beta)).
Defined.

Definition natequiv_inverse {A B : Type} `{IsGraph A} `{HasEquivs B}
  {F G : A -> B} `{!Is0Functor F, !Is0Functor G}
  : NatEquiv F G -> NatEquiv G F.
Proof.
  intros [alpha I].
  snapply Build_NatEquiv.
  1: exact (fun a => (alpha a)^-1$).
  snapply Build_Is1Natural'.
  +
 intros X Y f.
    apply vinverse, I.
  +
 intros X Y f.
    apply hinverse, I.
Defined.

Record Fun01 (A B : Type) `{IsGraph A} `{IsGraph B} := {
  fun01_F : A -> B;
  fun01_is0functor :: Is0Functor fun01_F;
}.

Coercion fun01_F : Fun01 >-> Funclass.

Arguments Build_Fun01 {A B isgraph_A isgraph_B} F {fun01_is0functor} : rename.
Arguments fun01_F {A B isgraph_A isgraph_B} : rename.
Definition Build_Fun01' {A B : Type} `{IsGraph A} `{IsGraph B}
  (F : A -> B) (fmap : forall a b (f : a $-> b), F a $-> F b)
  : Fun01 A B.
exact (Build_Fun01 F (fun01_is0functor:=Build_Is0Functor F fmap)).
Defined.

Instance isgraph_fun01 (A B : Type) `{IsGraph A} `{Is1Cat B} : IsGraph (Fun01 A B).
Proof.
  srapply Build_IsGraph.
  intros [F ?] [G ?].
  exact (NatTrans F G).
Defined.

Instance is01cat_fun01 (A B : Type) `{IsGraph A} `{Is1Cat B} : Is01Cat (Fun01 A B).
Proof.
  srapply Build_Is01Cat.
  -
 intros [F ?]; cbn.
    exact (nattrans_id F).
  -
 intros F G K gamma alpha; cbn in *.
    exact (nattrans_comp gamma alpha).
Defined.

Instance is2graph_fun01 (A B : Type) `{IsGraph A, Is1Cat B}
  : Is2Graph (Fun01 A B).
Proof.
  intros [F ?] [G ?]; apply Build_IsGraph.
  intros [alpha ?] [gamma ?].
  exact (forall a, alpha a $== gamma a).
Defined.

Instance is1cat_fun01 (A B : Type) `{IsGraph A} `{Is1Cat B} : Is1Cat (Fun01 A B).
Admitted.

Instance hasequivs_fun01 (A B : Type) `{Is01Cat A} `{HasEquivs B}
  : HasEquivs (Fun01 A B).
Proof.
  srapply Build_HasEquivs.
  1: intros F G; exact (NatEquiv F G).
  all: intros F G alpha; cbn in *.
  -
 exact (forall a, CatIsEquiv (alpha a)).
  -
 exact alpha.
  -
 intros a; exact _.
  -
 apply Build_NatEquiv'.
  -
 cbn; intros; apply cate_buildequiv_fun.
  -
 exact (natequiv_inverse alpha).
  -
 intros; apply cate_issect.
  -
 intros; apply cate_isretr.
  -
 intros [gamma ?] r s a; cbn in *.
    exact (catie_adjointify (alpha a) (gamma a) (r a) (s a)).
Defined.

Record Fun11 (A B : Type) `{Is1Cat A} `{Is1Cat B} :=
{
  fun11_fun : A -> B ;
  is0functor_fun11 :: Is0Functor fun11_fun ;
  is1functor_fun11 :: Is1Functor fun11_fun
}.

Coercion fun11_fun : Fun11 >-> Funclass.

Arguments Build_Fun11 A B
  {isgraph_A is2graph_A is01cat_A is1cat_A
   isgraph_B is2graph_B is01cat_B is1cat_B}
  F {is0functor_fun11 is1functor_fun11} : rename.

Coercion fun01_fun11 {A B : Type} `{Is1Cat A} `{Is1Cat B}
           (F : Fun11 A B)
  : Fun01 A B.
Proof.
  exists F; exact _.
Defined.
Instance isgraph_fun11 {A B : Type} `{Is1Cat A} `{Is1Cat B}
  : IsGraph (Fun11 A B).
exact (isgraph_induced fun01_fun11).
Defined.
Instance is01cat_fun11 {A B : Type} `{Is1Cat A} `{Is1Cat B}
  : Is01Cat (Fun11 A B).
exact (is01cat_induced fun01_fun11).
Defined.
Instance is2graph_fun11 {A B : Type} `{Is1Cat A, Is1Cat B}
  : Is2Graph (Fun11 A B).
exact (is2graph_induced fun01_fun11).
Defined.
Instance is1cat_fun11 {A B :Type} `{Is1Cat A} `{Is1Cat B}
  : Is1Cat (Fun11 A B).
exact (is1cat_induced fun01_fun11).
Defined.
Instance hasequivs_fun11 {A B : Type} `{Is1Cat A} `{HasEquivs B}
  : HasEquivs (Fun11 A B).
exact (hasequivs_induced fun01_fun11).
Defined.
Definition fun01_id {A} `{IsGraph A} : Fun01 A A.
exact (Build_Fun01 idmap).
Defined.
Definition fun01_compose {A B C} `{IsGraph A, IsGraph B, IsGraph C}
  : Fun01 B C -> Fun01 A B -> Fun01 A C.
exact (fun G F => Build_Fun01 (G o F)).
Defined.

Record Graph := {
  graph_carrier :> Type;
  isgraph_graph_carrier :: IsGraph graph_carrier
}.

Instance isgraph_graph : IsGraph Graph
  := { Hom A B := Fun01 A B }.
Instance is2graph_graph : Is2Graph Graph.
exact (fun A B => {| Hom F G := Transformation (fun01_F F) (fun01_F G) |}).
Defined.

Instance is01cat_graph : Is01Cat Graph := {
  Id A := fun01_id;
  cat_comp A B C G F := fun01_compose G F
}.

Scheme sum_rec := Minimality for sum Sort Type.
Arguments sum_rec {A B} P f g s : rename.
Instance isgraph_type@{u v} : IsGraph@{v u} Type@{u}.
exact (Build_IsGraph Type@{u} (fun a b => a -> b)).
Defined.

Instance is01cat_type : Is01Cat Type.
Proof.
  econstructor.
  +
 intro; exact idmap.
  +
 exact (fun a b c g f => g o f).
Defined.
Instance is2graph_type : Is2Graph Type.
exact (fun x y => Build_IsGraph _ (fun f g => f == g)).
Defined.

Instance is1cat_strong_type : Is1Cat_Strong Type.
Admitted.

Instance hasequivs_type : HasEquivs Type.
Proof.
  srefine (Build_HasEquivs Type _ _ _ _ Equiv (@IsEquiv) _ _ _ _ _ _ _ _); intros A B.
  all:intros f.
  -
 exact f.
  -
 exact _.
  -
 apply Build_Equiv.
  -
 intros; reflexivity.
  -
 intros; exact (f^-1).
  -
 cbn.
intros ?; apply eissect.
  -
 cbn.
intros ?; apply eisretr.
  -
 intros g r s; exact (isequiv_adjointify f g r s).
Defined.

Record ZeroGpd := {
  carrier :> Type;
  isgraph_carrier :: IsGraph carrier;
  is01cat_carrier :: Is01Cat carrier;
  is0gpd_carrier :: Is0Gpd carrier;
}.
Definition zerogpd_graph (C : ZeroGpd) : Graph.
exact ({|
    graph_carrier := carrier C;
    isgraph_graph_carrier := isgraph_carrier C
  |}).
Defined.
Instance isgraph_0gpd : IsGraph ZeroGpd.
exact (isgraph_induced zerogpd_graph).
Defined.
Instance is01cat_0gpd : Is01Cat ZeroGpd.
exact (is01cat_induced zerogpd_graph).
Defined.
Instance is2graph_0gpd : Is2Graph ZeroGpd.
exact (is2graph_induced zerogpd_graph).
Defined.

Instance is1cat_0gpd : Is1Cat ZeroGpd.
Admitted.
Instance hasequivs_0gpd : HasEquivs ZeroGpd.
exact (cat_hasequivs ZeroGpd).
Defined.
 Section GraphQuotient.
  Context {A : Type@{i}}.

  Private Inductive GraphQuotient (R : A -> A -> Type@{j}) : Type@{u} :=
  | gq : A -> GraphQuotient R.

  Arguments gq {R} a.

  Context {R : A -> A -> Type@{j}}.

  Axiom gqglue : forall {a b : A},
    R a b -> paths (@gq R a) (gq b).
Definition GraphQuotient_ind
    (P : GraphQuotient R -> Type@{k})
    (gq' : forall a, P (gq a))
    (gqglue' : forall a b (s : R a b), gqglue s # gq' a = gq' b)
    : forall x, P x.
exact (fun x =>
    match x with
    | gq a => fun _ => gq' a
    end gqglue').
Defined.

  Axiom GraphQuotient_ind_beta_gqglue
  : forall (P : GraphQuotient R -> Type@{k})
    (gq' : forall a, P (gq a))
    (gqglue' : forall a b (s : R a b), gqglue s # gq' a = gq' b)
    (a b: A) (s : R a b),
    apD (GraphQuotient_ind P gq' gqglue') (gqglue s) = gqglue' a b s.

 End GraphQuotient.

Arguments gq {A R} a.

Definition GraphQuotient_rec {A R P} (c : A -> P) (g : forall a b, R a b -> c a = c b)
  : GraphQuotient R -> P.
Proof.
  srapply GraphQuotient_ind.
  1: exact c.
  intros a b s.
  exact (transport_const _ _ @ g a b s).
Defined.

Definition GraphQuotient_rec_beta_gqglue {A R P}
  (c : A -> P) (g : forall a b, R a b -> c a = c b)
  (a b : A) (s : R a b)
  : ap (GraphQuotient_rec c g) (gqglue s) = g a b s.
Proof.
  unfold GraphQuotient_rec.
  refine (cancelL _ _ _ _ ).
  refine ((apD_const _ _)^ @ _).
  rapply GraphQuotient_ind_beta_gqglue.
Defined.
Definition Coeq@{i j u} {B : Type@{i}} {A : Type@{j}} (f g : B -> A) : Type@{u}.
exact (GraphQuotient@{i j u} (fun a b => {x : B & (f x = a) * (g x = b)})).
Defined.
Definition coeq {B A f g} (a : A) : @Coeq B A f g.
exact (gq a).
Defined.
Definition cglue {B A f g} b : @coeq B A f g (f b) = coeq (g b).
exact (gqglue (b; (idpath,idpath))).
Defined.
Arguments coeq : simpl never.

Definition Coeq_ind {B A f g} (P : @Coeq B A f g -> Type)
  (coeq' : forall a, P (coeq a))
  (cglue' : forall b, (cglue b) # (coeq' (f b)) = coeq' (g b))
  : forall w, P w.
Proof.
  rapply GraphQuotient_ind.
  intros a b [x [[] []]].
  exact (cglue' x).
Defined.

Definition Coeq_rec {B A f g} (P : Type) (coeq' : A -> P)
  (cglue' : forall b, coeq' (f b) = coeq' (g b))
  : @Coeq B A f g -> P.
Proof.
  rapply GraphQuotient_rec.
  intros a b [x [[] []]].
  exact (cglue' x).
Defined.

Definition Coeq_rec_beta_cglue {B A f g} (P : Type) (coeq' : A -> P)
  (cglue' : forall b:B, coeq' (f b) = coeq' (g b)) (b:B)
  : ap (Coeq_rec P coeq' cglue') (cglue b) = cglue' b.
Proof.
  rapply GraphQuotient_rec_beta_gqglue.
Defined.
Definition Pushout@{i j k l} {A : Type@{i}} {B : Type@{j}} {C : Type@{k}}
  (f : A -> B) (g : A -> C) : Type@{l}.
exact (Coeq@{l l _} (inl o f) (inr o g)).
Defined.
Definition push {A B C : Type} {f : A -> B} {g : A -> C}
 : B+C -> Pushout f g.
exact (@coeq _ _ (inl o f) (inr o g)).
Defined.
Definition pushl {A B C} {f : A -> B} {g : A -> C} (b : B)
  : Pushout f g.
exact (push (inl b)).
Defined.
Definition pushr {A B C} {f : A -> B} {g : A -> C} (c : C)
  : Pushout f g.
exact (push (inr c)).
Defined.

Definition pglue {A B C : Type} {f : A -> B} {g : A -> C} (a : A)
  : pushl (f a) = pushr (g a)
  := @cglue A (B+C) (inl o f) (inr o g) a.

Section PushoutInd.

  Context {A B C : Type} {f : A -> B} {g : A -> C}
    (P : Pushout f g -> Type)
    (pushb : forall b : B, P (pushl b))
    (pushc : forall c : C, P (pushr c))
    (pusha : forall a : A, (pglue a) # (pushb (f a)) = pushc (g a)).
Definition Pushout_ind
    : forall (w : Pushout f g), P w.
exact (Coeq_ind P (sum_ind (P o push) pushb pushc) pusha).
Defined.

End PushoutInd.
Definition Pushout_rec {A B C} {f : A -> B} {g : A -> C} (P : Type)
  (pushb : B -> P)
  (pushc : C -> P)
  (pusha : forall a : A, pushb (f a) = pushc (g a))
  : @Pushout A B C f g -> P.
exact (@Coeq_rec _ _ (inl o f) (inr o g) P (sum_rec P pushb pushc) pusha).
Defined.

Definition Pushout_rec_beta_pglue {A B C f g} (P : Type)
  (pushb : B -> P)
  (pushc : C -> P)
  (pusha : forall a : A, pushb (f a) = pushc (g a))
  (a : A)
  : ap (Pushout_rec P pushb pushc pusha) (pglue a) = pusha a.
Proof.
  napply Coeq_rec_beta_cglue.
Defined.
Definition opyon_0gpd {A : Type} `{Is1Cat A} (a : A) : A -> ZeroGpd.
exact (fun b => Build_ZeroGpd (a $-> b) _ _ _).
Defined.

Instance is0functor_opyon_0gpd {A : Type} `{Is1Cat A} (a : A)
  : Is0Functor (opyon_0gpd a).
Proof.
  apply Build_Is0Functor.
  intros b c f.
  exact (Build_Fun01 (cat_postcomp a f)).
Defined.

Instance is1functor_opyon_0gpd {A : Type} `{Is1Cat A} (a : A)
  : Is1Functor (opyon_0gpd a).
Admitted.

Definition opyoneda_0gpd {A : Type} `{Is1Cat A} (a : A)
           (F : A -> ZeroGpd) `{!Is0Functor F, !Is1Functor F}
  : F a -> (opyon_0gpd a $=> F).
Proof.
  intros x b.
  refine (Build_Fun01' (A:=opyon_0gpd a b) (B:=F b) (fun f => fmap F f x) _).
  intros f1 f2 h.
  exact (fmap2 F h x).
Defined.
Definition un_opyoneda_0gpd {A : Type} `{Is1Cat A}
  (a : A) (F : A -> ZeroGpd) {ff : Is0Functor F}
  : (opyon_0gpd a $=> F) -> F a.
exact (fun alpha => alpha a (Id a)).
Defined.

Definition opyoneda_isretr_0gpd {A : Type} `{Is1Cat A} (a : A)
  (F : A -> ZeroGpd) `{!Is0Functor F, !Is1Functor F}
  (alpha : opyon_0gpd a $=> F) {alnat : Is1Natural (opyon_0gpd a) F alpha}
  (b : A)
  : opyoneda_0gpd a F (un_opyoneda_0gpd a F alpha) b $== alpha b.
Admitted.
Definition opyon1_0gpd {A : Type} `{Is1Cat A} (a : A) : Fun11 A ZeroGpd.
exact (Build_Fun11 _ _ (opyon_0gpd a)).
Defined.

Definition opyon_equiv_0gpd {A : Type} `{HasEquivs A}
  {a b : A} (f : opyon1_0gpd a $<~> opyon1_0gpd b)
  : b $<~> a.
Proof.

  set (fa := (cate_fun f a) (Id a)).

  set (gb := (cate_fun f^-1$ b) (Id b)).

  srapply (cate_adjointify fa gb).

  -
 exact (opyoneda_isretr_0gpd _ _ f^-1$ a fa $@ cat_eissect (f a) (Id a)).
  -
 exact (opyoneda_isretr_0gpd _ _ f     b gb $@ cat_eisretr (f b) (Id b)).
Defined.

  Definition Join (A : Type@{i}) (B : Type@{j})
    := Pushout@{k i j k} (@fst A B) (@snd A B).
Definition joinl {A B} : A -> Join A B.
exact (fun a => @pushl (A*B) A B fst snd a).
Defined.
Definition joinr {A B} : B -> Join A B.
exact (fun b => @pushr (A*B) A B fst snd b).
Defined.

  Definition jglue {A B} a b : joinl a = joinr b
    := @pglue (A*B) A B fst snd (a , b).

  Definition Join_ind {A B : Type} (P : Join A B -> Type)
    (P_A : forall a, P (joinl a)) (P_B : forall b, P (joinr b))
    (P_g : forall a b, transport P (jglue a b) (P_A a) = P_B b)
    : forall (x : Join A B), P x.
  Proof.
    apply (Pushout_ind P P_A P_B).
    exact (fun ab => P_g (fst ab) (snd ab)).
  Defined.

  Definition Join_rec {A B P : Type} (P_A : A -> P) (P_B : B -> P)
    (P_g : forall a b, P_A a = P_B b) : Join A B -> P.
  Proof.
    apply (Pushout_rec P P_A P_B).
    exact (fun ab => P_g (fst ab) (snd ab)).
  Defined.

  Definition Join_rec_beta_jglue {A B P : Type} (P_A : A -> P)
    (P_B : B -> P) (P_g : forall a b, P_A a = P_B b) a b
    : ap (Join_rec P_A P_B P_g) (jglue a b) = P_g a b.
  Proof.
    exact (Pushout_rec_beta_pglue _ _ _ _ (a, b)).
  Defined.

Record JoinRecData {A B P : Type} := {
    jl : A -> P;
    jr : B -> P;
    jg : forall a b, jl a = jr b;
  }.

Arguments JoinRecData : clear implicits.
Arguments Build_JoinRecData {A B P}%_type_scope (jl jr jg)%_function_scope.
Definition join_rec {A B P : Type} (f : JoinRecData A B P)
  : Join A B $-> P.
Admitted.

Definition joinrecdata_fun {A B P Q : Type} (g : P -> Q) (f : JoinRecData A B P)
  : JoinRecData A B Q.
Proof.
  snapply Build_JoinRecData.
  -
 exact (g o jl f).
  -
 exact (g o jr f).
  -
 exact (fun a b => ap g (jg f a b)).
Defined.

Record JoinRecPath {A B P : Type} {f g : JoinRecData A B P} := {
    hl : forall a, jl f a = jl g a;
    hr : forall b, jr f b = jr g b;
    hg : forall a b, jg f a b @ hr b = hl a @ jg g a b;
  }.

Arguments JoinRecPath {A B P} f g.

Definition bundle_joinrecpath {A B P : Type} {jl' : A -> P} {jr' : B -> P}
  {f g : forall a b, jl' a = jr' b}
  (h : forall a b, f a b = g a b)
  : JoinRecPath (Build_JoinRecData jl' jr' f) (Build_JoinRecData jl' jr' g).
Admitted.

Ltac bundle_joinrecpath :=
  hnf;
  match goal with |- JoinRecPath ?F ?G =>
    refine (bundle_joinrecpath (f:=jg F) (g:=jg G) _) end.

Ltac generalize_three f a b :=
  let fg := fresh in let fr := fresh in let fl := fresh in
  destruct f as [fl fr fg]; cbn;
  generalize (fg a b); clear fg;
  generalize (fr b); clear fr;
  generalize (fl a); clear fl.

Ltac interval_ind f a b :=
  generalize_three f a b;
  intro f;
  apply paths_ind.

Definition square_ind {P : Type} (a b : P) (ab : a = b)
  (Q : forall (a' b' : P) (ab' : a' = b') (ha : a = a') (hb : b = b') (k : ab @ hb = ha @ ab'), Type)
  (s : Q a b ab idpath idpath (equiv_p1_1q idpath))
  : forall a' b' ab' ha hb k, Q a' b' ab' ha hb k.
Admitted.

Global Ltac square_ind g h a b :=
  generalize_three h a b;
  generalize_three g a b;
  apply square_ind.
Instance isgraph_joinrecdata (A B P : Type) : IsGraph (JoinRecData A B P).
exact ({| Hom := JoinRecPath |}).
Defined.

Instance is01cat_joinrecdata (A B P : Type) : Is01Cat (JoinRecData A B P).
Admitted.

Instance is0gpd_joinrecdata (A B P : Type) : Is0Gpd (JoinRecData A B P).
Admitted.
Definition joinrecdata_0gpd (A B P : Type) : ZeroGpd.
exact (Build_ZeroGpd (JoinRecData A B P) _ _ _).
Defined.

Instance is0functor_joinrecdata_fun {A B P Q : Type} (g : P -> Q)
  : Is0Functor (@joinrecdata_fun A B P Q g).
Admitted.

Instance is0functor_joinrecdata_0gpd (A B : Type) : Is0Functor (joinrecdata_0gpd A B).
Proof.
  apply Build_Is0Functor.
  intros P Q g.
  exact (Build_Fun01 (joinrecdata_fun g)).
Defined.

Instance is1functor_joinrecdata_0gpd (A B : Type) : Is1Functor (joinrecdata_0gpd A B).
Admitted.
Definition joinrecdata_0gpd_fun (A B : Type) : Fun11 Type ZeroGpd.
exact (Build_Fun11 _ _ (joinrecdata_0gpd A B)).
Defined.

Definition join_rec_inv_natequiv (A B : Type)
  : NatEquiv (opyon_0gpd (Join A B)) (joinrecdata_0gpd_fun A B).
Admitted.

Definition join_rec_natequiv (A B : Type)
  := natequiv_inverse (join_rec_inv_natequiv A B).

Section Triangle.

  Context {A B : Type}.

  Definition triangle_v (a : A) {b b' : B} (p : b = b')
    : jglue a b @ ap joinr p = jglue a b'.
Admitted.

End Triangle.
Definition functor_join {A B C D} (f : A -> C) (g : B -> D)
    : Join A B -> Join C D.
Admitted.

  #[export] Instance isequiv_functor_join {A B C D}
    (f : A -> C) `{!IsEquiv f} (g : B -> D) `{!IsEquiv g}
    : IsEquiv (functor_join f g).
Admitted.
Definition equiv_functor_join {A B C D} (f : A <~> C) (g : B <~> D)
    : Join A B <~> Join C D.
exact (Build_Equiv _ _ (functor_join f g) _).
Defined.

  Definition joinrecdata_sym (A B P : Type)
    : joinrecdata_0gpd A B P $-> joinrecdata_0gpd B A P.
  Proof.
    snapply Build_Fun01'.

    -
 intros [fl fr fg].
      snapply (Build_JoinRecData fr fl).
      intros b a; exact (fg a b)^.

    -
 intros f g h; simpl.
      snapply Build_JoinRecPath; simpl.
      1, 2: intros; apply h.
      intros b a.
      square_ind g h a b.
      by interval_ind f a b.
  Defined.

  Definition joinrecdata_sym_inv (A B P : Type)
    : joinrecdata_sym B A P $o joinrecdata_sym A B P $== Id _.
Admitted.

  Definition joinrecdata_sym_natequiv (A B : Type)
    : NatEquiv (joinrecdata_0gpd_fun A B) (joinrecdata_0gpd_fun B A).
  Proof.
    snapply Build_NatEquiv.

    -
 intro P.
      snapply cate_adjointify.
      1, 2: apply joinrecdata_sym.
      1, 2: apply joinrecdata_sym_inv.

    -
 snapply Build_Is1Natural.
      intros P Q g f; simpl.
      bundle_joinrecpath.
      intros b a; simpl.
      symmetry; apply ap_V.
  Defined.
Definition joinrecdata_fun_sym (A B : Type)
    : NatEquiv (opyon_0gpd (Join A B)) (opyon_0gpd (Join B A)).
exact (natequiv_compose (join_rec_natequiv B A)
        (natequiv_compose (joinrecdata_sym_natequiv A B) (join_rec_inv_natequiv A B))).
Defined.

  Definition equiv_join_sym' (A B : Type)
    : Join A B <~> Join B A.
  Proof.
    tapply (opyon_equiv_0gpd (A:=Type)).
    apply joinrecdata_fun_sym.
  Defined.
Definition join_sym_recdata (A B : Type)
    : JoinRecData A B (Join B A).
exact (Build_JoinRecData joinr joinl (fun a b => (jglue b a)^)).
Defined.
Definition join_sym (A B : Type)
    : Join A B -> Join B A.
exact (join_rec (join_sym_recdata A B)).
Defined.

  Definition join_sym_homotopic (A B : Type)
    : join_sym A B == equiv_join_sym' A B.
Admitted.
Definition equiv_join_sym (A B : Type) : Join A B <~> Join B A.
exact (equiv_homotopic_inverse (equiv_join_sym' A B)
                              (join_sym_homotopic A B)
                              (join_sym_homotopic B A)).
Defined.

Section TriJoinStructure.
  Context {A B C : Type}.

  Definition TriJoin := Join A (Join B C).
Definition join1 : A -> TriJoin.
exact (joinl).
Defined.
Definition join2 : B -> TriJoin.
exact (fun b => (joinr (joinl b))).
Defined.
Definition join3 : C -> TriJoin.
exact (fun c => (joinr (joinr c))).
Defined.
Definition join12 : forall a b, join1 a = join2 b.
exact (fun a b => jglue a (joinl b)).
Defined.
Definition join13 : forall a c, join1 a = join3 c.
exact (fun a c => jglue a (joinr c)).
Defined.
Definition join23 : forall b c, join2 b = join3 c.
exact (fun b c => ap joinr (jglue b c)).
Defined.
End TriJoinStructure.

Arguments TriJoin A B C : clear implicits.
Definition ap_triangle {X Y} (f : X -> Y)
  {a b c : X} {ab : a = b} {bc : b = c} {ac : a = c} (abc : ab @ bc = ac)
  : ap f ab @ ap f bc = ap f ac.
Admitted.

Definition ap_trijoin {A B C P : Type} (f : TriJoin A B C -> P)
  (a : A) (b : B) (c : C)
  : ap f (join12 a b) @ ap f (join23 b c) = ap f (join13 a c).
Admitted.

Definition ap_trijoin_V {A B C P : Type} (f : TriJoin A B C -> P)
  (a : A) (b : B) (c : C)
  : ap_triangle f (triangle_v a (jglue b c)^)
     = (1 @@ (ap (ap f) (ap_V joinr _) @ ap_V f _)) @ moveR_pV _ _ _ (ap_trijoin f a b c)^.
Admitted.

Record TriJoinRecData {A B C P : Type} := {
    j1 : A -> P;
    j2 : B -> P;
    j3 : C -> P;
    j12 : forall a b, j1 a = j2 b;
    j13 : forall a c, j1 a = j3 c;
    j23 : forall b c, j2 b = j3 c;
    j123 : forall a b c, j12 a b @ j23 b c = j13 a c;
  }.

Arguments TriJoinRecData : clear implicits.
Arguments Build_TriJoinRecData {A B C P}%_type_scope (j1 j2 j3 j12 j13 j23 j123)%_function_scope.

Definition trijoin_rec {A B C P : Type} (f : TriJoinRecData A B C P)
  : TriJoin A B C $-> P.
Proof.
  snapply Join_rec.
  -
 exact (j1 f).
  -
 snapply Join_rec.
    +
 exact (j2 f).
    +
 exact (j3 f).
    +
 exact (j23 f).
  -
 intro a.
    snapply Join_ind; cbn beta.
    +
 exact (j12 f a).
    +
 exact (j13 f a).
    +
 intros b c.
      lhs napply transport_paths_Fr.
      exact (1 @@ Join_rec_beta_jglue _ _ _ _ _ @ j123 f a b c).
Defined.
Definition trijoin_rec_beta_join12 {A B C P : Type} (f : TriJoinRecData A B C P) (a : A) (b : B)
  : ap (trijoin_rec f) (join12 a b) = j12 f a b.
exact (Join_rec_beta_jglue _ _ _ _ _).
Defined.
Definition trijoin_rec_beta_join13 {A B C P : Type} (f : TriJoinRecData A B C P) (a : A) (c : C)
  : ap (trijoin_rec f) (join13 a c) = j13 f a c.
Admitted.

Definition trijoin_rec_beta_join23 {A B C P : Type} (f : TriJoinRecData A B C P) (b : B) (c : C)
  : ap (trijoin_rec f) (join23 b c) = j23 f b c.
Admitted.

Definition trijoin_rec_beta_join123 {A B C P : Type} (f : TriJoinRecData A B C P)
  (a : A) (b : B) (c : C)
  : ap_trijoin (trijoin_rec f) a b c
    = (trijoin_rec_beta_join12 f a b @@ trijoin_rec_beta_join23 f b c)
        @ j123 f a b c @ (trijoin_rec_beta_join13 f a c)^.
Admitted.

Definition trijoinrecdata_fun {A B C P Q : Type} (g : P -> Q) (f : TriJoinRecData A B C P)
  : TriJoinRecData A B C Q.
Proof.
  snapply Build_TriJoinRecData.
  -
 exact (g o j1 f).
  -
 exact (g o j2 f).
  -
 exact (g o j3 f).
  -
 exact (fun a b => ap g (j12 f a b)).
  -
 exact (fun a c => ap g (j13 f a c)).
  -
 exact (fun b c => ap g (j23 f b c)).
  -
 intros a b c; cbn beta.
    exact (ap_triangle g (j123 f a b c)).

Defined.

Definition prism {P : Type}
  {a b c : P} {ab : a = b} {ac : a = c} {bc : b = c} (abc : ab @ bc = ac)
  {a' b' c' : P} {ab' : a' = b'} {ac' : a' = c'} {bc' : b' = c'} (abc' : ab' @ bc' = ac')
  {k1 : a = a'} {k2 : b = b'} {k3 : c = c'}
  (k12 : ab @ k2 = k1 @ ab') (k13 : ac @ k3 = k1 @ ac') (k23 : bc @ k3 = k2 @ bc')
  := concat_p_pp _ _ _ @ whiskerR abc k3 @ k13
    = whiskerL ab k23
    @ concat_p_pp _ _ _ @ whiskerR k12 bc'
    @ concat_pp_p _ _ _ @ whiskerL k1 abc'.

Record TriJoinRecPath {A B C P : Type} {f g : TriJoinRecData A B C P} := {
    h1 : forall a, j1 f a = j1 g a;
    h2 : forall b, j2 f b = j2 g b;
    h3 : forall c, j3 f c = j3 g c;
    h12 : forall a b, j12 f a b @ h2 b = h1 a @ j12 g a b;
    h13 : forall a c, j13 f a c @ h3 c = h1 a @ j13 g a c;
    h23 : forall b c, j23 f b c @ h3 c = h2 b @ j23 g b c;
    h123 : forall a b c, prism (j123 f a b c) (j123 g a b c) (h12 a b) (h13 a c) (h23 b c);
  }.

Arguments TriJoinRecPath {A B C P} f g.

Record TriJoinRecData' {A B C P : Type} {j1' : A -> P} {j2' : B -> P} {j3' : C -> P} := {
    j12' : forall a b, j1' a = j2' b;
    j13' : forall a c, j1' a = j3' c;
    j23' : forall b c, j2' b = j3' c;
    j123' : forall a b c, j12' a b @ j23' b c = j13' a c;
  }.

Arguments TriJoinRecData' {A B C P} j1' j2' j3'.
Arguments Build_TriJoinRecData' {A B C P}%_type_scope
  (j1' j2' j3' j12' j13' j23' j123')%_function_scope.

Definition prism' {P : Type} {a b c : P}
  {ab : a = b} {ac : a = c} {bc : b = c} (abc : ab @ bc = ac)
  {ab' : a = b} {ac' : a = c} {bc' : b = c} (abc' : ab' @ bc' = ac')
  (k12 : ab = ab') (k13 : ac = ac') (k23 : bc = bc')
  := abc @ k13 = (k12 @@ k23) @ abc'.

Record TriJoinRecPath' {A B C P : Type} {j1' : A -> P} {j2' : B -> P} {j3' : C -> P}
  {f g : TriJoinRecData' j1' j2' j3'} := {
    h12' : forall a b, j12' f a b = j12' g a b;
    h13' : forall a c, j13' f a c = j13' g a c;
    h23' : forall b c, j23' f b c = j23' g b c;
    h123' : forall a b c, prism' (j123' f a b c) (j123' g a b c) (h12' a b) (h13' a c) (h23' b c);
  }.

Arguments TriJoinRecPath' {A B C P} {j1' j2' j3'} f g.
Definition bundle_trijoinrecdata {A B C P : Type} {j1' : A -> P} {j2' : B -> P} {j3' : C -> P}
  (f : TriJoinRecData' j1' j2' j3')
  : TriJoinRecData A B C P.
exact (Build_TriJoinRecData j1' j2' j3' (j12' f) (j13' f) (j23' f) (j123' f)).
Defined.
Definition unbundle_trijoinrecdata {A B C P : Type} (f : TriJoinRecData A B C P)
  : TriJoinRecData' (j1 f) (j2 f) (j3 f).
exact (Build_TriJoinRecData' (j1 f) (j2 f) (j3 f) (j12 f) (j13 f) (j23 f) (j123 f)).
Defined.

Definition bundle_trijoinrecpath {A B C P : Type} {j1' : A -> P} {j2' : B -> P} {j3' : C -> P}
  {f g : TriJoinRecData' j1' j2' j3'} (h : TriJoinRecPath' f g)
  : TriJoinRecPath (bundle_trijoinrecdata f) (bundle_trijoinrecdata g).
Admitted.

Ltac bundle_trijoinrecpath :=
  hnf;
  match goal with |- TriJoinRecPath ?F ?G =>
    refine (bundle_trijoinrecpath (f:=unbundle_trijoinrecdata F)
                                  (g:=unbundle_trijoinrecdata G) _) end;
  snapply Build_TriJoinRecPath'.
Instance isgraph_trijoinrecdata (A B C P : Type) : IsGraph (TriJoinRecData A B C P).
exact ({| Hom := TriJoinRecPath |}).
Defined.

Instance is0functor_trijoin_rec (A B C P : Type) : Is0Functor (@trijoin_rec A B C P).
Admitted.

Definition trijoin_rec_nat (A B C : Type) {P Q : Type} (g : P -> Q)
  (f : TriJoinRecData A B C P)
  : trijoin_rec (trijoinrecdata_fun g f) $== g o trijoin_rec f.
Admitted.

Definition functor_join_join_rec {A B C A' P} (f : A -> A') (g : JoinRecData B C P)
  : functor_join f (join_rec g)
    == trijoin_rec {| j1 := joinl o f; j2 := joinr o jl g; j3 := joinr o jr g;
                      j12 := fun a b => jglue (f a) (jl g b);
                      j13 := fun a c => jglue (f a) (jr g c);
                      j23 := fun b c => ap joinr (jg g b c);
                      j123 := fun a b c => triangle_v (f a) (jg g b c); |}.
Admitted.
Definition trijoin_id_sym A B C : TriJoin A B C <~> TriJoin A C B.
exact (equiv_functor_join equiv_idmap (equiv_join_sym B C)).
Defined.

Definition trijoinrecdata_id_sym {A B C P} (f : TriJoinRecData A B C P)
  : TriJoinRecData A C B P.
Proof.
  snapply (Build_TriJoinRecData (j1 f) (j3 f) (j2 f)); intros.
  -
 apply (j13 f).
  -
 apply (j12 f).
  -
 symmetry; apply (j23 f).
  -
 cbn beta.
 apply moveR_pV; symmetry.
    apply (j123 f).
Defined.

Definition trijoin_rec_id_sym {A B C P} (f : TriJoinRecData A C B P)
  : trijoin_rec f o trijoin_id_sym A B C == trijoin_rec (trijoinrecdata_id_sym f).
Proof.

  etransitivity.
  {
 refine (cat_postwhisker (A:=Type) (trijoin_rec f) _).
    apply functor_join_join_rec.
}
  unfold join_sym_recdata, jl, jr, jg.

  refine ((trijoin_rec_nat A B C (trijoin_rec f) _)^$ $@ _).
  refine (fmap trijoin_rec _).

  bundle_trijoinrecpath; intros; cbn.
  -
 apply trijoin_rec_beta_join13.
  -
 apply trijoin_rec_beta_join12.
  -
 lhs refine (ap _ (ap_V _ _)).
    lhs refine (ap_V (trijoin_rec f) _).
    apply (ap inverse).
    apply trijoin_rec_beta_join23.
  -
 unfold prism'.
    rewrite ap_trijoin_V.
    rewrite trijoin_rec_beta_join123.
    set (f' := f).
    destruct f as [f1 f2 f3 f12 f13 f23 f123]; timeout 2 cbn.
Abort.
