(* A universe polymorphic, cumulative hierarchy of packed classes with primitive projections, in the
   shape Hierarchy Builder generates for math-comp's algebra: mixins parametrized by the mixins
   they depend on, flattened classes, a forgetful instance for each pair of structures, structures
   over a ring (two universes) and linear maps (three universes). Its proofs compare universe
   levels as math-comp's do: rewriting in instances on small types equates universes with Set,
   and sections whose universes are distinct but equal make the kernel check these equalities at
   each use of their lemmas. [-d loop-checking-merged] checks that the levels equal in all
   valuations are merged, so that [check_eq] on levels only compares canonical nodes. *)

From Corelib Require Import ssreflect ssrfun ssrbool.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Warnings "-redundant-canonical-projection".
Set Debug "loop-checking-merged".

(** Mixins *)

Record hasEq (T : Type) := HasEq {
  eq_op : T -> T -> bool;
  eq_opP : forall x y, reflect (x = y) (eq_op x y) }.

Record hasZero (T : Type) := HasZero { zero : T }.
Record hasAdd (T : Type) := HasAdd { add : T -> T -> T }.
Record hasOpp (T : Type) := HasOpp { opp : T -> T }.

Record isNmodule (T : Type) (z : hasZero T) (a : hasAdd T) := IsNmodule {
  addrA : forall x y w, add a x (add a y w) = add a (add a x y) w;
  addrC : forall x y, add a x y = add a y x;
  add0r : forall x, add a (zero z) x = x }.

Record isZmodule (T : Type) (z : hasZero T) (a : hasAdd T) (o : hasOpp T) := IsZmodule {
  addNr : forall x, add a (opp o x) x = zero z }.

Record isRing (T : Type) (z : hasZero T) (a : hasAdd T) := IsRing {
  one : T;
  mul : T -> T -> T;
  mulrA : forall x y w, mul x (mul y w) = mul (mul x y) w;
  mul1r : forall x, mul one x = x;
  mulr1 : forall x, mul x one = x;
  mulrDl : forall x y w, mul (add a x y) w = add a (mul x w) (mul y w);
  mulrDr : forall x y w, mul x (add a y w) = add a (mul x y) (mul x w) }.

Record isComRing (T : Type) (z : hasZero T) (a : hasAdd T) (r : isRing z a) := IsComRing {
  mulrC : forall x y, mul r x y = mul r y x }.

(** Structures *)

Module Eq.
Record axioms_ (T : Type) := Class { eq_mixin : hasEq T }.
Record type := Pack { sort : Type; class : axioms_ sort }.
End Eq.
Coercion Eq.sort : Eq.type >-> Sortclass.

Module Nmod.
Record axioms_ (T : Type) := Class {
  eq_mixin : hasEq T; zero_mixin : hasZero T; add_mixin : hasAdd T;
  nmod_mixin : isNmodule zero_mixin add_mixin }.
Record type := Pack { sort : Type; class : axioms_ sort }.
End Nmod.
Coercion Nmod.sort : Nmod.type >-> Sortclass.

Module Zmod.
Record axioms_ (T : Type) := Class {
  eq_mixin : hasEq T; zero_mixin : hasZero T; add_mixin : hasAdd T; opp_mixin : hasOpp T;
  nmod_mixin : isNmodule zero_mixin add_mixin;
  zmod_mixin : isZmodule zero_mixin add_mixin opp_mixin }.
Record type := Pack { sort : Type; class : axioms_ sort }.
End Zmod.
Coercion Zmod.sort : Zmod.type >-> Sortclass.

Module Ring.
Record axioms_ (T : Type) := Class {
  eq_mixin : hasEq T; zero_mixin : hasZero T; add_mixin : hasAdd T; opp_mixin : hasOpp T;
  nmod_mixin : isNmodule zero_mixin add_mixin;
  zmod_mixin : isZmodule zero_mixin add_mixin opp_mixin;
  ring_mixin : isRing zero_mixin add_mixin }.
Record type := Pack { sort : Type; class : axioms_ sort }.
End Ring.
Coercion Ring.sort : Ring.type >-> Sortclass.

Module ComRing.
Record axioms_ (T : Type) := Class {
  eq_mixin : hasEq T; zero_mixin : hasZero T; add_mixin : hasAdd T; opp_mixin : hasOpp T;
  nmod_mixin : isNmodule zero_mixin add_mixin;
  zmod_mixin : isZmodule zero_mixin add_mixin opp_mixin;
  ring_mixin : isRing zero_mixin add_mixin;
  comring_mixin : isComRing ring_mixin }.
Record type := Pack { sort : Type; class : axioms_ sort }.
End ComRing.
Coercion ComRing.sort : ComRing.type >-> Sortclass.

(** Forgetful instances, one for each pair of structures as Hierarchy Builder declares them, keyed
  on the sort of the richer structure *)

Definition Eq_of_Nmod (T : Nmod.type) : Eq.type := Eq.Pack (Eq.Class (Nmod.eq_mixin (Nmod.class T))).
Canonical Eq_of_Nmod.
Coercion Eq_of_Nmod : Nmod.type >-> Eq.type.

Definition Eq_of_Zmod (T : Zmod.type) : Eq.type := Eq.Pack (Eq.Class (Zmod.eq_mixin (Zmod.class T))).
Canonical Eq_of_Zmod.
Definition Nmod_of_Zmod (T : Zmod.type) : Nmod.type :=
  let c := Zmod.class T in Nmod.Pack (Nmod.Class (Zmod.eq_mixin c) (Zmod.nmod_mixin c)).
Canonical Nmod_of_Zmod.
Coercion Nmod_of_Zmod : Zmod.type >-> Nmod.type.

Definition Eq_of_Ring (T : Ring.type) : Eq.type := Eq.Pack (Eq.Class (Ring.eq_mixin (Ring.class T))).
Canonical Eq_of_Ring.
Definition Nmod_of_Ring (T : Ring.type) : Nmod.type :=
  let c := Ring.class T in Nmod.Pack (Nmod.Class (Ring.eq_mixin c) (Ring.nmod_mixin c)).
Canonical Nmod_of_Ring.
Definition Zmod_of_Ring (T : Ring.type) : Zmod.type :=
  let c := Ring.class T in
  Zmod.Pack (Zmod.Class (Ring.eq_mixin c) (Ring.nmod_mixin c) (Ring.zmod_mixin c)).
Canonical Zmod_of_Ring.
Coercion Zmod_of_Ring : Ring.type >-> Zmod.type.

Definition Eq_of_ComRing (T : ComRing.type) : Eq.type :=
  Eq.Pack (Eq.Class (ComRing.eq_mixin (ComRing.class T))).
Canonical Eq_of_ComRing.
Definition Nmod_of_ComRing (T : ComRing.type) : Nmod.type :=
  let c := ComRing.class T in Nmod.Pack (Nmod.Class (ComRing.eq_mixin c) (ComRing.nmod_mixin c)).
Canonical Nmod_of_ComRing.
Definition Zmod_of_ComRing (T : ComRing.type) : Zmod.type :=
  let c := ComRing.class T in
  Zmod.Pack (Zmod.Class (ComRing.eq_mixin c) (ComRing.nmod_mixin c) (ComRing.zmod_mixin c)).
Canonical Zmod_of_ComRing.
Definition Ring_of_ComRing (T : ComRing.type) : Ring.type :=
  let c := ComRing.class T in
  Ring.Pack (Ring.Class (ComRing.eq_mixin c) (ComRing.nmod_mixin c) (ComRing.zmod_mixin c)
    (ComRing.ring_mixin c)).
Canonical Ring_of_ComRing.
Coercion Ring_of_ComRing : ComRing.type >-> Ring.type.

(** Operations, through the structures as in math-comp *)

Definition eqb {T : Eq.type} : T -> T -> bool := eq_op (Eq.eq_mixin (Eq.class T)).
Definition zeror {T : Nmod.type} : T := zero (Nmod.zero_mixin (Nmod.class T)).
Definition addr {T : Nmod.type} : T -> T -> T := add (Nmod.add_mixin (Nmod.class T)).
Definition oppr {T : Zmod.type} : T -> T := opp (Zmod.opp_mixin (Zmod.class T)).
Definition oner {T : Ring.type} : T := one (Ring.ring_mixin (Ring.class T)).
Definition mulr {T : Ring.type} : T -> T -> T := mul (Ring.ring_mixin (Ring.class T)).

Declare Scope ring_scope.
Delimit Scope ring_scope with R.
Local Open Scope ring_scope.
Notation "0" := zeror : ring_scope.
Notation "1" := oner : ring_scope.
Infix "+" := addr : ring_scope.
Notation "- x" := (oppr x) : ring_scope.
Notation "x - y" := (x + - y) : ring_scope.
Infix "*" := mulr : ring_scope.
Infix "==" := eqb (at level 70).

(** Generic theory *)

Lemma eqP {T : Eq.type} (x y : T) : reflect (x = y) (x == y).
Proof. exact: eq_opP. Qed.

Section NmodTheory.
Variable V : Nmod.type.
Implicit Types x y z t : V.
Lemma addrA' x y z : x + (y + z) = x + y + z.
Proof. exact: (addrA (Nmod.nmod_mixin (Nmod.class V))). Qed.
Lemma addrC' x y : x + y = y + x.
Proof. exact: (addrC (Nmod.nmod_mixin (Nmod.class V))). Qed.
Lemma add0r' x : 0 + x = x.
Proof. exact: (add0r (Nmod.nmod_mixin (Nmod.class V))). Qed.
Lemma addr0' x : x + 0 = x.
Proof. by rw addrC' add0r'. Qed.
Lemma addrCA x y z : x + (y + z) = y + (x + z).
Proof. by rw !addrA' (addrC' x y). Qed.
Lemma addrAC x y z : x + y + z = x + z + y.
Proof. by rw -!addrA' (addrC' y z). Qed.
Lemma addrACA x y z t : x + y + (z + t) = x + z + (y + t).
Proof. by rw -!addrA' (addrCA y z t). Qed.
End NmodTheory.

Section ZmodTheory.
Variable V : Zmod.type.
Implicit Types x y z : V.
Lemma addNr' x : - x + x = 0.
Proof. exact: (addNr (Zmod.zmod_mixin (Zmod.class V))). Qed.
Lemma addrN x : x - x = 0.
Proof. by rw addrC' addNr'. Qed.
Lemma addKr x y : - x + (x + y) = y.
Proof. by rw addrA' addNr' add0r'. Qed.
Lemma addNKr x y : x + (- x + y) = y.
Proof. by rw addrA' addrN add0r'. Qed.
Lemma addrK x y : x + y - y = x.
Proof. by rw -addrA' addrN addr0'. Qed.
Lemma addrI x y z : x + y = x + z -> y = z.
Proof. by move=> H; rw -(addKr x y) H addKr. Qed.
Lemma oppr0 : - (0 : V) = 0.
Proof. by rw -(addr0' (- 0)) addNr'. Qed.
Lemma opprK x : - - x = x.
Proof. by apply: (@addrI (- x)); rw addrN addNr'. Qed.
Lemma opprD x y : - (x + y) = - x - y.
Proof. by apply: (@addrI (x + y)); rw addrN addrACA !addrN addr0'. Qed.
End ZmodTheory.

Section RingTheory.
Variable R : Ring.type.
Implicit Types x y z : R.
Lemma mulrA' x y z : x * (y * z) = x * y * z.
Proof. exact: (mulrA (Ring.ring_mixin (Ring.class R))). Qed.
Lemma mul1r' x : 1 * x = x.
Proof. exact: (mul1r (Ring.ring_mixin (Ring.class R))). Qed.
Lemma mulr1' x : x * 1 = x.
Proof. exact: (mulr1 (Ring.ring_mixin (Ring.class R))). Qed.
Lemma mulrDl' x y z : (x + y) * z = x * z + y * z.
Proof. exact: (mulrDl (Ring.ring_mixin (Ring.class R))). Qed.
Lemma mulrDr' x y z : x * (y + z) = x * y + x * z.
Proof. exact: (mulrDr (Ring.ring_mixin (Ring.class R))). Qed.
Lemma mul0r x : 0 * x = 0.
Proof. by apply: (@addrI _ (0 * x)); rw -mulrDl' !addr0'. Qed.
Lemma mulr0 x : x * 0 = 0.
Proof. by apply: (@addrI _ (x * 0)); rw -mulrDr' !addr0'. Qed.
Lemma mulrN x y : x * - y = - (x * y).
Proof. by apply: (@addrI _ (x * y)); rw -mulrDr' !addrN mulr0. Qed.
Lemma mulNr x y : - x * y = - (x * y).
Proof. by apply: (@addrI _ (x * y)); rw -mulrDl' !addrN mul0r. Qed.
Lemma mulrNN x y : - x * - y = x * y.
Proof. by rw mulrN mulNr opprK. Qed.
Lemma mulrBl x y z : (x - y) * z = x * z - y * z.
Proof. by rw mulrDl' mulNr. Qed.
Lemma mulrBr x y z : x * (y - z) = x * y - x * z.
Proof. by rw mulrDr' mulrN. Qed.
End RingTheory.

Section ComRingTheory.
Variable R : ComRing.type.
Implicit Types x y z t : R.
Lemma mulrC' x y : x * y = y * x.
Proof. exact: (mulrC (ComRing.comring_mixin (ComRing.class R))). Qed.
Lemma mulrCA x y z : x * (y * z) = y * (x * z).
Proof. by rw !mulrA' (mulrC' x y). Qed.
Lemma mulrAC x y z : x * y * z = x * z * y.
Proof. by rw -!mulrA' (mulrC' y z). Qed.
Lemma mulrACA x y z t : x * y * (z * t) = x * z * (y * t).
Proof. by rw -!mulrA' (mulrCA y z t). Qed.
Lemma sqrrD x y : (x + y) * (x + y) = x * x + (y * x + y * x) + y * y.
Proof. by rw mulrDl' !mulrDr' (mulrC' x y) !addrA'. Qed.
Lemma subr_sqr x y : x * x - y * y = (x - y) * (x + y).
Proof. by rw mulrBl !mulrDr' (mulrC' y x) opprD -addrA' addNKr. Qed.
End ComRingTheory.

(** Modules over a ring, with two universes as [GRing.Lmodule.type@{u u0} R] *)

Record isLmodule (R : Ring.type) (V : Type) (z : hasZero V) (a : hasAdd V) := IsLmodule {
  scale : R -> V -> V;
  scalerA : forall c d v, scale c (scale d v) = scale (c * d) v;
  scale1r : forall v, scale 1 v = v;
  scalerDr : forall c u v, scale c (add a u v) = add a (scale c u) (scale c v);
  scalerDl : forall v c d, scale (c + d) v = add a (scale c v) (scale d v) }.

Module Lmod.
Record axioms_ (R : Ring.type) (V : Type) := Class {
  eq_mixin : hasEq V; zero_mixin : hasZero V; add_mixin : hasAdd V; opp_mixin : hasOpp V;
  nmod_mixin : isNmodule zero_mixin add_mixin;
  zmod_mixin : isZmodule zero_mixin add_mixin opp_mixin;
  lmod_mixin : isLmodule R zero_mixin add_mixin }.
Record type (R : Ring.type) := Pack { sort : Type; class : axioms_ R sort }.
End Lmod.
Coercion Lmod.sort : Lmod.type >-> Sortclass.

Definition Eq_of_Lmod R (V : Lmod.type R) : Eq.type :=
  Eq.Pack (Eq.Class (Lmod.eq_mixin (Lmod.class V))).
Canonical Eq_of_Lmod.
Definition Nmod_of_Lmod R (V : Lmod.type R) : Nmod.type :=
  let c := Lmod.class V in Nmod.Pack (Nmod.Class (Lmod.eq_mixin c) (Lmod.nmod_mixin c)).
Canonical Nmod_of_Lmod.
Definition Zmod_of_Lmod R (V : Lmod.type R) : Zmod.type :=
  let c := Lmod.class V in
  Zmod.Pack (Zmod.Class (Lmod.eq_mixin c) (Lmod.nmod_mixin c) (Lmod.zmod_mixin c)).
Canonical Zmod_of_Lmod.
Coercion Zmod_of_Lmod : Lmod.type >-> Zmod.type.

Definition scaler {R : Ring.type} {V : Lmod.type R} : R -> V -> V :=
  scale (Lmod.lmod_mixin (Lmod.class V)).
Notation "c *: v" := (scaler c v) (at level 40) : ring_scope.

Section LmodTheory.
Variables (R : Ring.type) (V : Lmod.type R).
Implicit Types (c d : R) (u v : V).
Lemma scalerA' c d v : c *: (d *: v) = (c * d) *: v.
Proof. exact: (scalerA (Lmod.lmod_mixin (Lmod.class V))). Qed.
Lemma scale1r' v : 1 *: v = v.
Proof. exact: (scale1r (Lmod.lmod_mixin (Lmod.class V))). Qed.
Lemma scalerDr' c u v : c *: (u + v) = c *: u + c *: v.
Proof. exact: (scalerDr (Lmod.lmod_mixin (Lmod.class V))). Qed.
Lemma scalerDl' v c d : (c + d) *: v = c *: v + d *: v.
Proof. exact: (scalerDl (Lmod.lmod_mixin (Lmod.class V))). Qed.
Lemma scale0r v : 0 *: v = 0.
Proof. by apply: (@addrI _ (0 *: v)); rw -scalerDl' !addr0'. Qed.
Lemma scaler0 c : c *: (0 : V) = 0.
Proof. by apply: (@addrI _ (c *: 0)); rw -scalerDr' !addr0'. Qed.
Lemma scaleNr c v : - c *: v = - (c *: v).
Proof. by apply: (@addrI _ (c *: v)); rw -scalerDl' !addrN scale0r. Qed.
Lemma scalerN c v : c *: - v = - (c *: v).
Proof. by apply: (@addrI _ (c *: v)); rw -scalerDr' !addrN scaler0. Qed.
Lemma scaleN1r v : - (1 : R) *: v = - v.
Proof. by rw scaleNr scale1r'. Qed.
End LmodTheory.

(** Linear maps, with three universes as [GRing.Linear.type@{u u0 u1}] *)

Record linear (R : Ring.type) (U V : Lmod.type R) := Linear {
  lfun :> U -> V;
  linearP : forall c u v, lfun (c *: u + v) = c *: lfun u + lfun v }.

Section LinearTheory.
Variables (R : Ring.type) (U V W : Lmod.type R).
Lemma linear0 (f : linear U V) : f 0 = 0.
Proof.
  have H := linearP f 1 0 0; rw !scale1r' addr0' in H.
  by apply: (@addrI _ (f 0)); rw addr0' -H.
Qed.
Lemma linearD (f : linear U V) u v : f (u + v) = f u + f v.
Proof. by rw -[u]scale1r' linearP !scale1r'. Qed.
Lemma linearZ (f : linear U V) c u : f (c *: u) = c *: f u.
Proof. by rw -[c *: u]addr0' linearP linear0 addr0'. Qed.
Lemma linearN (f : linear U V) u : f (- u) = - f u.
Proof. by rw -scaleN1r linearZ scaleN1r. Qed.
Lemma linearB (f : linear U V) u v : f (u - v) = f u - f v.
Proof. by rw linearD linearN. Qed.
Lemma comp_linearP (f : linear V W) (g : linear U V) c u v :
  f (g (c *: u + v)) = c *: f (g u) + f (g v).
Proof. by rw !linearP. Qed.
Definition comp_lin (f : linear V W) (g : linear U V) : linear U W :=
  @Linear _ _ _ (fun u => f (g u)) (comp_linearP f g).
Definition id_lin : linear U U := @Linear _ _ _ (fun u => u) (fun _ _ _ => erefl).
End LinearTheory.

Lemma comp_linA (R : Ring.type) (T U V W : Lmod.type R)
  (f : linear V W) (g : linear U V) (h : linear T U) x :
  comp_lin (comp_lin f g) h x = comp_lin f (comp_lin g h) x.
Proof. by []. Qed.

Lemma comp_lin_id (R : Ring.type) (U V : Lmod.type R) (f : linear U V) x :
  comp_lin f (id_lin U) x = f x /\ comp_lin (id_lin V) f x = f x.
Proof. by []. Qed.

(** Instances: booleans, products of rings, a ring as a module over itself, products of modules *)

Definition bool_eq (a b : bool) := if a then b else ~~ b.
Lemma bool_eqP (x y : bool) : reflect (x = y) (bool_eq x y).
Proof. by case: x; case: y; constructor. Qed.
Definition bool_eqMixin := HasEq bool_eqP.
Definition bool_zero := HasZero false.
Definition bool_add := HasAdd xorb.
Definition bool_opp := HasOpp (fun b : bool => b).
Lemma bool_nmod : isNmodule bool_zero bool_add.
Proof. by split; repeat case. Qed.
Lemma bool_zmod : isZmodule bool_zero bool_add bool_opp.
Proof. by split; repeat case. Qed.
Definition bool_ring : isRing bool_zero bool_add.
Proof. by apply: (@IsRing _ _ _ true andb); repeat case. Defined.
Lemma bool_comring : isComRing bool_ring.
Proof. by split; repeat case. Qed.

Canonical bool_Eq := Eq.Pack (Eq.Class bool_eqMixin).
Canonical bool_Nmod := Nmod.Pack (Nmod.Class bool_eqMixin bool_nmod).
Canonical bool_Zmod := Zmod.Pack (Zmod.Class bool_eqMixin bool_nmod bool_zmod).
Canonical bool_Ring := Ring.Pack (Ring.Class bool_eqMixin bool_nmod bool_zmod bool_ring).
Canonical bool_ComRing := ComRing.Pack (ComRing.Class bool_eqMixin bool_nmod bool_zmod bool_comring).

Section ProdRing.
Variables R1 R2 : ComRing.type.
Implicit Types x y w : R1 * R2.
Definition prod_eq x y := (x.1 == y.1) && (x.2 == y.2).
Lemma prod_eqP x y : reflect (x = y) (prod_eq x y).
Proof.
  case: x y => [a1 a2] [b1 b2]; rw /prod_eq /=.
  case: (eqP a1 b1) => [->|ne1]; case: (eqP a2 b2) => [->|ne2]; constructor; congruence.
Qed.
Definition prod_zero : R1 * R2 := (0, 0).
Definition prod_add x y := (x.1 + y.1, x.2 + y.2).
Definition prod_opp x := (- x.1, - x.2).
Definition prod_one : R1 * R2 := (1, 1).
Definition prod_mul x y := (x.1 * y.1, x.2 * y.2).
Lemma prod_addA x y w : prod_add x (prod_add y w) = prod_add (prod_add x y) w.
Proof. by rw /prod_add /= !addrA'. Qed.
Lemma prod_addC x y : prod_add x y = prod_add y x.
Proof. by rw /prod_add (addrC' x.1) (addrC' x.2). Qed.
Lemma prod_add0 x : prod_add prod_zero x = x.
Proof. by case: x => a b; rw /prod_add /= !add0r'. Qed.
Lemma prod_addN x : prod_add (prod_opp x) x = prod_zero.
Proof. by case: x => a b; rw /prod_add /= !addNr'. Qed.
Lemma prod_mulA x y w : prod_mul x (prod_mul y w) = prod_mul (prod_mul x y) w.
Proof. by rw /prod_mul /= !mulrA'. Qed.
Lemma prod_mul1 x : prod_mul prod_one x = x.
Proof. by case: x => a b; rw /prod_mul /= !mul1r'. Qed.
Lemma prod_mulr1 x : prod_mul x prod_one = x.
Proof. by case: x => a b; rw /prod_mul /= !mulr1'. Qed.
Lemma prod_mulDl x y w : prod_mul (prod_add x y) w = prod_add (prod_mul x w) (prod_mul y w).
Proof. by rw /prod_mul /prod_add /= !mulrDl'. Qed.
Lemma prod_mulDr x y w : prod_mul x (prod_add y w) = prod_add (prod_mul x y) (prod_mul x w).
Proof. by rw /prod_mul /prod_add /= !mulrDr'. Qed.
Lemma prod_mulC x y : prod_mul x y = prod_mul y x.
Proof. by rw /prod_mul (mulrC' x.1) (mulrC' x.2). Qed.

Definition prod_eqMixin := HasEq prod_eqP.
Definition prod_nmod := @IsNmodule _ (HasZero prod_zero) (HasAdd prod_add) prod_addA prod_addC prod_add0.
Definition prod_zmod := @IsZmodule _ (HasZero prod_zero) (HasAdd prod_add) (HasOpp prod_opp) prod_addN.
Definition prod_ring := @IsRing _ (HasZero prod_zero) (HasAdd prod_add) prod_one prod_mul
  prod_mulA prod_mul1 prod_mulr1 prod_mulDl prod_mulDr.
Definition prod_comring := @IsComRing _ _ _ prod_ring prod_mulC.

Canonical prod_Eq := Eq.Pack (Eq.Class prod_eqMixin).
Canonical prod_Nmod := Nmod.Pack (Nmod.Class prod_eqMixin prod_nmod).
Canonical prod_Zmod := Zmod.Pack (Zmod.Class prod_eqMixin prod_nmod prod_zmod).
Canonical prod_Ring := Ring.Pack (Ring.Class prod_eqMixin prod_nmod prod_zmod prod_ring).
Canonical prod_ComRing := ComRing.Pack (ComRing.Class prod_eqMixin prod_nmod prod_zmod prod_comring).
End ProdRing.

Section RegularModule.
Variable R : ComRing.type.
Definition regular_lmod :=
  @IsLmodule R R (Ring.zero_mixin (Ring.class R)) (Ring.add_mixin (Ring.class R)) mulr (@mulrA' R) (@mul1r' R)
  (@mulrDr' R) (fun v c d => mulrDl' c d v).
Canonical regular_Lmod := Lmod.Pack (Lmod.Class (Ring.eq_mixin (Ring.class R))
  (Ring.nmod_mixin (Ring.class R)) (Ring.zmod_mixin (Ring.class R)) regular_lmod).
End RegularModule.

(** Uses at several universes: canonical instances of products, nested in each other and in the
  structures over a ring, as in math-comp's algebraic examples *)

Lemma prod_sqrrD (x y : (bool * bool) * bool) : (x + y) * (x + y) = x * x + (y * x + y * x) + y * y.
Proof. exact: sqrrD. Qed.

Lemma prod_subr_sqr (R : ComRing.type) (x y : R * (R * bool)) : x * x - y * y = (x - y) * (x + y).
Proof. exact: subr_sqr. Qed.

Lemma prod_mulrACA (R S : ComRing.type) (x y z t : (R * S) * (S * R)) :
  x * y * (z * t) = x * z * (y * t).
Proof. exact: mulrACA. Qed.

Lemma prod_opprD (R S : ComRing.type) (x y : R * (S * (R * S))) : - (x + y) = - x - y.
Proof. exact: opprD. Qed.

Lemma regular_scale (R : ComRing.type) (c d : R) (v : regular_Lmod R) :
  c *: (d *: v) = (c * d) *: v.
Proof. exact: scalerA'. Qed.

Lemma regular_prod_scale (R S : ComRing.type) (c : R * S) (v : regular_Lmod (prod_ComRing R S)) :
  - c *: v = - (c *: v).
Proof. exact: scaleNr. Qed.

Lemma lin_comp (R : ComRing.type) (U V W : Lmod.type R) (f : linear U V) (g : linear V W) c u v :
  comp_lin g f (c *: u - v) = c *: g (f u) - g (f v).
Proof. by rw /= !linearB !linearZ. Qed.

Lemma lin_comp_regular (R S : ComRing.type) (V : Lmod.type (prod_ComRing R S))
  (f : linear (regular_Lmod (prod_ComRing R S)) V) (g : linear V V) c u v :
  comp_lin g (comp_lin g f) (c *: u + v) = c *: g (g (f u)) + g (g (f v)).
Proof. by rw /= !linearD !linearZ. Qed.

Lemma lin_sum (R : ComRing.type) (U V : Lmod.type R) (f g : linear U V) c u v :
  f (c *: u - v) + g (c *: u - v) = c *: (f u + g u) - (f v + g v).
Proof. by rw !linearB !linearZ scalerDr' opprD !addrA' (addrAC _ (- f v)). Qed.

(** Rewriting with the generic theory in concrete instances on small types, which equates the
  universes of the structures with [Set], as in math-comp's proofs on finite groups *)

Section Concrete.
Implicit Types (b : bool) (p q r : bool * bool) (s t : (bool * bool) * (bool * bool)).

Lemma bool_ex1 b c : (b + c) * (b + c) - c * c = b * b + (c * b + c * b).
Proof. by rw sqrrD addrK. Qed.
Lemma bool_ex2 b c : - (b * - c) = b * c.
Proof. by rw mulrN opprK. Qed.
Lemma prod_ex1 p q : (p - q) * (p + q) = p * p - q * q.
Proof. by rw subr_sqr. Qed.
Lemma prod_ex2 p q r : p * (q * r) + - (q * (p * r)) = 0.
Proof. by rw mulrCA addrN. Qed.
Lemma prod_ex3 p q r : (p + q) * r - q * r = p * r.
Proof. by rw mulrDl' addrK. Qed.
Lemma prod_ex4 s t : - (s + t) + t = - s.
Proof. by rw opprD -addrA' addNr' addr0'. Qed.
Lemma prod_ex5 s t : s * t * (t * s) = s * s * (t * t).
Proof. by rw (mulrC' t s) mulrACA. Qed.
Lemma prod_ex6 s t : (s + t) * (s + t) - t * t = s * s + (t * s + t * s).
Proof. by rw sqrrD addrK. Qed.
Lemma prod_ex7 p q : - p * - q - p * q = 0.
Proof. by rw mulrNN addrN. Qed.
Lemma prod_ex8 s t : s * (t - t) = 0.
Proof. by rw addrN mulr0. Qed.
Lemma prod_ex9 (x y : bool * (bool * (bool * bool))) : x * y - y * x = 0.
Proof. by rw (mulrC' x y) addrN. Qed.
Lemma prod_ex10 (x y : (bool * bool) * (bool * (bool * bool))) : - (x * y) + x * y = 0.
Proof. by rw addNr'. Qed.
Lemma scale_ex1 (c d : bool * bool) (v : regular_Lmod (prod_ComRing bool_ComRing bool_ComRing)) :
  c *: (d *: v) - (c * d) *: v = 0.
Proof. by rw scalerA' addrN. Qed.
Lemma scale_ex2 (c : bool * bool) (u v : regular_Lmod (prod_ComRing bool_ComRing bool_ComRing)) :
  c *: (u - v) = c *: u - c *: v.
Proof. by rw scalerDr' scalerN. Qed.
Lemma lin_ex1 (U : Lmod.type bool_Ring) (f g : linear U U) (c : bool) u v :
  comp_lin f g (c *: u - v) = c *: f (g u) - f (g v).
Proof. by rw /= !linearB !linearZ. Qed.
Lemma lin_ex2 (V : Lmod.type (prod_Ring bool_ComRing bool_ComRing))
  (f : linear (regular_Lmod (prod_ComRing bool_ComRing bool_ComRing)) V) c u :
  f (c *: u) - c *: f u = 0.
Proof. by rw linearZ addrN. Qed.
End Concrete.

(** Sections whose universes are distinct but equal, as when math-comp's lemmas on
  [Variables (aT rT : finGroupType)] force them to be shared: each lemma of the section keeps
  the equality, which the kernel checks at each use of the lemma *)

Section SharedUniverses.
Universes u v.
Constraint u = v.
Variables (R : ComRing.type) (U : Lmod.type@{_ u} R) (V : Lmod.type@{_ v} R).
Variables (f : linear U V) (g : linear V U).

Lemma shared_D x y : g (f (x + y)) = g (f x) + g (f y).
Proof. by rw !linearD. Qed.
Lemma shared_Z c x : comp_lin g f (c *: x) = c *: comp_lin g f x.
Proof. exact: linearZ. Qed.
Lemma shared_B x y : comp_lin f (comp_lin g f) (x - y) = f (g (f x)) - f (g (f y)).
Proof. by rw /= !linearB. Qed.
Lemma shared_D3 x y z : g (f (x + y + z)) = g (f x) + g (f y) + g (f z).
Proof. by rw !shared_D. Qed.
End SharedUniverses.

Section SharedUniverses2.
Universes u' v'.
Constraint u' = v'.
Variables (R : ComRing.type) (U : Lmod.type@{_ u'} R) (V : Lmod.type@{_ v'} R).
Variables (f : linear U V) (g : linear V U).

Lemma shared2_D x y z t : g (f (x + y + z + t)) = g (f x) + g (f y) + g (f z) + g (f t).
Proof. by rw !shared_D. Qed.
Lemma shared2_Z c d x : comp_lin g f (c *: (d *: x)) = c *: (d *: comp_lin g f x).
Proof. by rw !shared_Z. Qed.
Lemma shared2_B x y : comp_lin f (comp_lin g f) (x - y) + f (g (f y)) = f (g (f x)).
Proof. by rw shared_B -addrA' addNr' addr0'. Qed.
Lemma shared2_D3 x y z : g (f (x + y + z)) - g (f z) = g (f x) + g (f y).
Proof. by rw shared_D3 addrK. Qed.
End SharedUniverses2.
