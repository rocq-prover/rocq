(* To run: [dune build theories/Force && dune exec -- dev/shim/coqc test.v] *)

Require Import Force.Force.

(**** UNIVERSES ****)

Definition check_run@{u1 u2} : forall (T : Type@{u1}) (K : Type@{u2}), Blocked T -> (T -> K) -> K := @run.
Inductive sunit : SProp := sitt.
Fail Check (@run@{SProp Type; Set Set} sunit nat (block sitt) (fun _ => 0)).
Definition check_Blocked@{u} : Type@{u} -> Type@{u} := Blocked.
Definition check_block@{u} : forall (T : Type@{u}), T -> Blocked@{Type;u} T := @block.
Definition check_unblock@{u} : forall (T : Type@{u}), Blocked@{Type;u} T -> T := @unblock.

(**** SORTS ****)

#[universes(polymorphic)] Definition type_of@{s;u} {T : Type@{s;u}} (t : T) := T.
Definition unblock_prop_type (b : Blocked@{Prop;_} (tt = tt)) : Type := type_of (unblock@{Prop;_} b).
Definition blocked_prop_type : Blocked@{Type;_} Type := @block@{Type;_} Type (tt = tt).

(**** EVALUATION ****)

Ltac syn_refl := lazymatch goal with |- ?t = ?t => exact eq_refl end.
Notation LAZY t := (ltac:(let x := eval lazy in t in exact x)) (only parsing).
Notation WHNF t := (ltac:(let x := eval lazy head in t in exact x)) (only parsing).

Goal LAZY (@block) = @block.
Proof. syn_refl. Qed.

Goal WHNF (@block) = @block.
Proof. syn_refl. Qed.

Goal LAZY (@block nat) = @block nat.
Proof. syn_refl. Qed.

Goal WHNF (@block nat) = @block nat.
Proof. syn_refl. Qed.

Goal WHNF (@block (id nat)) = @block (id nat).
Proof. syn_refl. Qed.

Goal LAZY (@block (id nat)) = @block nat.
Proof. syn_refl. Qed.

Goal WHNF (block 0) = block 0.
Proof. syn_refl. Qed.

Goal LAZY (block 0) = block 0.
Proof. syn_refl. Qed.

Goal WHNF (block (0 + 0)) = block (0 + 0).
Proof. syn_refl. Qed.

Goal LAZY (block (0 + 0)) = block (0 + 0).
Proof. syn_refl. Qed.

Goal WHNF (id (block (0 + 0))) = block (0 + 0).
Proof. syn_refl. Qed.

Goal LAZY (id (block (0 + 0))) = block (0 + 0).
Proof. syn_refl. Qed.

Goal WHNF (block (unblock (let x := 0 + 0 in block x))) = block 0.
Proof. syn_refl. Qed.

(* ... *)

Goal LAZY ((fun f => f (1 + 1)) block) = block 2.
Proof. syn_refl. Qed.

Goal LAZY ((fun f => f (1 + 1)) (fun x => block x)) = block 2.
Proof. syn_refl. Qed.

Goal WHNF ((fun f => f (1 + 1)) block) = block (1+1).
Proof. syn_refl. Qed.

Goal WHNF ((fun f => f (1 + 1)) (fun x => block x)) = block (1 + 1).
Proof. syn_refl. Qed.

Inductive True := I.
Definition id : True -> True := fun x => x.

Definition g := fun x:True => x.
Definition h := fun x:True => x.
Axiom and : True -> True -> True.
Axiom Pr : True -> Prop.

(* Non-lexical unblock is just a "projection" *)
Goal WHNF ((fun f => f (block (id I = id I))) unblock) = (id I = id I).
Proof. syn_refl. Qed.

(* Non-lexical run is just a "projection" *)
Goal WHNF ((fun f => f (block (id I = id I)) (fun x => x)) run) = (id I = id I).
Proof. syn_refl. Qed.

Goal WHNF (block (unblock (let x := (and (g I) (h I)) in block x))) = (block (and I I)).
Proof. syn_refl. Qed.

Goal WHNF (unblock (let x := (fun x : id I = I => True) in block x)) = (fun x : I = I => True).
Proof. syn_refl. Qed.

Goal WHNF (unblock (let x := forall x : id I = I, True in block x)) = (forall x : I = I, True).
Proof. syn_refl. Qed.

Goal WHNF (unblock (let x := id I in block (forall u:unit, x = x))) = (forall (u:unit), I = I).
Proof. syn_refl. Qed.

Goal WHNF (unblock (let x := 1 + 1 in block x)) = 2.
Proof. syn_refl. Qed.

Goal WHNF (run (block (1+1)) (fun x => x)) = WHNF (match 1 + 1 with S x => S x | 0 => 0 end).
Proof. syn_refl. Qed.

Goal WHNF (block (run (let n := I in block n) (fun x : True => x)))
        = (block (run (let n := I in block n) (fun x : True => x))).
Proof. syn_refl. Qed.

Goal WHNF (block (run (let x := (fun x => x) tt in block x) (fun x => x)))
        = (block (run (let x := (fun x => x) tt in block x) (fun x => x))).
Proof. syn_refl. Qed.

Goal WHNF (block (unblock (let x := (fun x => x) tt in block x))) = block tt.
Proof. syn_refl. Qed.

(*
block (unblock (let x := (fun x => x) tt in block x)) @ ε | ∅ --{whnf}-->
block @ (unblock (let x := (fun x => x) tt in block x)) . ε | ∅ --{whnf}-->

  unblock (let x := (fun x => x) tt in block x) @ ε | ∅ --{id}-->
  unblock @ (let x := (fun x => x) tt in block x) . ε | ∅ --{id}-->

    let x := (fun x => x) tt in block x @ ε | ∅ --{full}-->
    block x @ ε | ∅[x{full} := <(fun x => x) tt, ∅>] --{full}-->

      x @ ε | ∅[x{full} := <(fun x => x) tt, ∅>] --{id}-->

        (λ x => x) tt @ ε | ∅ --{full}-->
        λ x => x @ tt . ε | ∅ --{full}-->
        x @ ε | ∅[x{full} := <tt, ∅>] --{full}-->

          tt @ ε | ∅ --{full}--> (value)

        tt @ ε | ∅[x{full} := <tt, ∅>] --{full}--> (value)

      tt @ ε | ∅[x{full} := <tt, ∅>] --{id}--> (value, updated closure)

    block tt @ ε | ∅[x{full} := <tt, ∅>] --{full}-->

  unblock @ block tt . ε | ∅ --{id}-->
  tt @ ε | ∅ --{id}-->

block @ tt . ε | ∅ --{whnf}--> (done)
*)

Goal WHNF (block (run (let n := 2 + 2 in block n) (fun x : nat => 2 * 1)))
        = (block (run (let n := 2 + 2 in block n) (fun x : nat => 2 * 1))).
        (* = (block ((fun _ : nat => 2 * 1) 4)). *)
Proof. syn_refl. Qed.

Goal WHNF (block (run ((fun n => block n) (2 + 2)) (fun x : nat => 2 * 1)))
        = (block (run ((fun n => block n) (2 + 2)) (fun x : nat => 2 * 1))).
        (* = (block ((fun _ : nat => 2 * 1) 4)). *)
Proof. syn_refl. Qed.

Inductive n := N | O.
Definition a (x y : n) :=
  match x with
  | N => y
  | O => O
  end.
Goal WHNF (block (unblock ((fun x => block (a x O)) (a N N)))) = block (a N O).
Proof. syn_refl. Qed.

Goal WHNF (block (unblock ((fun x => block x) (a N N)))) = block (N).
Proof. syn_refl. Qed.

Goal WHNF (block (run ((fun n => block (n + 1)) (2 + 2)) (fun x : nat => 2 * 1)))
        = (block (run ((fun n => block (n + 1)) (2 + 2)) (fun x : nat => 2 * 1))).
        (* = (block ((fun _ : nat => 2 * 1) (4 + 1))). *)
Proof. syn_refl. Qed.

Goal WHNF (block (unblock (let n := 0 + 0 in block (n + n))))
        = block (0 + 0).
Proof. syn_refl. Qed.

Goal WHNF (block (unblock (let n := 0 + 0 in block (1 + unblock (let m := 0 + 0 in block (1 + m))))))
        = block (1 + (1 + 0)).
Proof. syn_refl. Qed.

Goal WHNF (block (unblock (
                      let n := 0 + 0 in
                      block (1 + n + unblock (
                                     let m := 2 + 2 in
                                     block (1 + m + unblock (
                                                        let k := 3 + 3 in
                                                        block (1 + n + m + k))))))))
        = block (1 + 0 + (1 + 4 + (1 + 0 + 4 + 6))).
Proof. syn_refl. Qed.

Goal LAZY (run (block (1 + 1)) (fun x => x + x)) = 4.
Proof. syn_refl. Qed.

Goal LAZY (run (block (1 + 1)) (fun x => x + x)) = 4.
Proof. syn_refl. Qed.

Goal LAZY (run (block (1 + 1)) (fun x => x + x)) = 4.
Proof. syn_refl. Qed.

Goal LAZY (block (2 + 2)) = block (2 + 2).
Proof. syn_refl. Qed.

Goal LAZY (unblock (block 42)) = 42.
Proof. syn_refl. Qed.

Goal LAZY (unblock (block (2 + 2))) = 4.
Proof. syn_refl. Qed.

Goal LAZY (unblock ((fun _ => block (2 + 2)) tt)) = 4.
Proof. syn_refl. Qed.

Goal LAZY (block (fun x => (2 + 2) + x)) = block (fun x => (2 + 2) + x).
Proof. syn_refl. Qed.

Goal LAZY (unblock (block (fun x => (2 + 2) + x))) = fun x => S (S (S (S x))).
Proof. syn_refl. Qed.

Goal WHNF (run (let x := 1 + 1 in block (x + 1)) (fun x => forall y, y = x))
        = forall y, y = 2 + 1.
Proof. syn_refl. Qed.

Set Printing Width 1000.
Section AllArgs.
  Context (b : Blocked (nat -> nat)).

  Goal LAZY (unblock b 0) = unblock b 0.
  Proof. syn_refl. Qed.

  Goal WHNF (unblock b 0) = unblock b 0.
  Proof. syn_refl. Qed.

  Goal LAZY (run b (fun x n => n) 0) = run b (fun x n => n) 0.
  Proof. syn_refl. Qed.

  Goal WHNF (run b (fun x n => n) 0) = run b (fun x n => n) 0.
  Proof. syn_refl. Qed.
End AllArgs.

Goal LAZY (unblock (block (fun x => block x)) (0 + 0)) = block (0).
Proof. syn_refl. Qed.

Goal WHNF (unblock (block (fun x => block x)) (0 + 0)) = block (0 + 0).
Proof. syn_refl. Qed.

Goal LAZY (run (block (fun x => block x)) (fun f x => f x) (0 + 0)) = block (0).
Proof. syn_refl. Qed.

Goal WHNF (run (block (fun x => block x)) (fun f x => f x) (0 + 0)) = block (0 + 0).
Proof. syn_refl. Qed.

Axiom F : run (let x := id I in block (id x)) (fun x => forall y, y = x).
Goal I=I.
  Succeed refine (F I).
  Succeed apply (F I).
  Succeed eapply (F I).
  Succeed exact (F I).
  Succeed eexact (F I).
  exact (F I).
Qed.

Module FunctionTypes.
  (* The example below should not call reduction on [id id R] _at all_! *)
  Inductive D := | d.
  Inductive R := | r (b: D).
  Definition id (x:Set) := x.
  Eval lazy head in @unblock R (let f := (fun x : id (id R) => block x) in @block R (@unblock R (f (r d)))).
End FunctionTypes.

Module Conversion.
  Axiom not : Prop -> Prop.
  Axiom TODO: forall {A:Prop}, A.

  Lemma test p :
    (forall _ : True, @unblock Prop (block (not p))).
    exact (@TODO (forall _ : True, not p)).
  Qed.
End Conversion.

Module Bla.
  Inductive prop :=.
  Axiom TODO: forall {A}, A.
  Definition reflect (p:prop) : Blocked Prop := match p with end.
  Lemma simplify_ok (p : prop) : False <-> unblock (reflect p).
  Proof.
    lazy.                       (* Used to fail *)
    destruct p.
  Qed.
End Bla.

(* Double substitution due to [Zrun] *)
Module Ind.
  Axiom P : nat -> Blocked Prop.
  Axiom x : nat.
  Axiom nat_ind_2 : forall P : nat -> Prop, (forall n : nat, True -> P (S n)) -> forall n : nat, P n.

  Goal forall n, (run (P n) (fun p => p)).
  Proof.
    refine (@nat_ind_2 (fun n => run (P n) (fun p => p)) _).
    intros n IHn.
    (* [Zrun]'s substitution was re-applied to the head in [zip_term] leading to wrong [REL]s. *)
    Fail lazymatch goal with |- context [P (S IHn)] => idtac end.
    lazymatch goal with |- context [P (S n)] => idtac end.
  Abort.
End Ind.

Module Proper.

Require Import Corelib.Classes.RelationClasses.
Require Import Corelib.Classes.Morphisms.
Require Import Corelib.Setoids.Setoid.

(* #[universes(polymorphic=yes,cumulative)] Record Blocked {T:Type} := block { unblock : T }. *)
(* #[global] Arguments Blocked : clear implicits. *)
(* #[global] Arguments block {_}. *)
(* #[global] Arguments unblock {_}. *)
(* Add Printing Constructor Blocked. *)
(* #[universes(polymorphic=yes)] Definition run : forall (T K : Type), Blocked T -> (T -> K) -> K := fun _ _ b f => f (unblock b). *)
(* #[global] Arguments run {_ _} _ _. *)

Require Export Force.Force.


#[local] Set Universe Polymorphism.
#[local] Unset Universe Minimization ToSet.

Class Equiv (T : Type) := equiv :  T -> T -> Prop.
Arguments equiv {_ _}.


#[global] Instance Blocked_equiv {T} : Equiv T -> Equiv (Blocked T) :=
  fun equiv a b => equiv (unblock a) (unblock b).

(* Regression tests for conversion of stacks containing [unblock] and [run].
   The primitive operator universe instance is stored under the local closure
   substitution; conversion must apply that substitution before comparing it. *)
Definition unblock_stack_substitution {T} {R : Equiv T} :
  Proper (@equiv (Blocked T) (Blocked_equiv R) ==> @equiv T R) (@unblock T) :=
  fun x y H => H.

Definition Run_equiv {T K} (R : Equiv K) (k : T -> K) : Equiv (Blocked T) :=
  fun a b => @equiv K R (@run T K a k) (@run T K b k).

Definition run_stack_substitution {T K} {R : Equiv K} (k : T -> K) :
  forall x y : Blocked T,
    @equiv (Blocked T) (Run_equiv R k) x y ->
    @equiv K R (@run T K x k) (@run T K y k) :=
  fun x y H => H.

#[global] Instance Blocked_equivalance {T} {R:Equiv T} : Equivalence R -> Equivalence (@equiv (Blocked T) _).
Proof.
  intros H.
  split.
  - destruct H as [H _ _]. repeat intro. apply H.
  - destruct H as [_ H _]. repeat intro. apply H. apply H0.
  - destruct H as [_ _ H]. repeat intro. refine (H _ _ _ _ _); eauto.
Qed.

#[global] Instance block_Proper {T} {R:Equiv T} : Proper (equiv ==> equiv) (@block T).
Proof. repeat intro. eauto. Qed.

#[global] Instance unblock_Proper {T} {R:Equiv T} : Proper (@equiv (Blocked T) _ ==> @equiv T _) (@unblock T).
Proof. lazy. repeat intro. exact H. Qed.

Lemma Blocked_ind_beta {T} (P : Blocked T -> Type) (IH : forall t : T, P (block t)) (t : T) :
  @Blocked_ind T P IH (block t) = IH t.
Proof. reflexivity. Qed.

Eval compute in @Blocked_ind nat (fun _ => nat) (fun n => S n) (block 0).

Lemma Blocked_eta {T} (t: Blocked T) : block (unblock t) = t.
Proof.
  refine (@Blocked_ind T (fun t => block (unblock t) = t) _ t).
  intro x; reflexivity.
Qed.

End Proper.


(* Port of stdpp telescopes *)
Module Telescopes.
#[local] Set Universe Polymorphism.
#[local] Set Polymorphic Inductive Cumulativity.
Set Printing Universes.

Inductive tele@{u u1} : Type@{u1} :=
  | TeleO : tele
  | TeleS {X : Blocked@{Type;u1} Type@{u}} (binder : unblock X -> tele) : tele.

#[global] Arguments TeleS {_} _.

Fixpoint tele_fun (TT : tele) (T : Type) : Type :=
  match TT with
  | TeleO => T
  | TeleS b => forall x, tele_fun (b x) T
  end.

Notation "TT -t> A" :=
  (tele_fun TT A) (at level 99, A at level 200, right associativity).

Definition tele_fold {X Y} {TT : tele} (step : forall {A : Type}, (A -> Y) -> Y) (base : X -> Y)
  : (TT -t> X) -> Y :=
  (fix rec {TT} : (TT -t> X) -> Y :=
     match TT as TT return (TT -t> X) -> Y with
     | TeleO => fun x : X => base x
     | TeleS b => fun f => step (fun x => rec (f x))
     end) TT.
Global Arguments tele_fold {_ _ !_} _ _ _ /.

Record tele_arg_cons {X : Type} (f : X -> Type) : Type := TeleArgCons
  { tele_arg_head : X;
    tele_arg_tail : f tele_arg_head }.
Global Arguments TeleArgCons {_ _} _ _.

Fixpoint tele_arg@{u u1} (t : tele@{u u1}) : Type@{u} :=
  match t with
  | TeleO => unit
  | TeleS f => tele_arg_cons (fun x => tele_arg (f x))
  end.
Global Arguments tele_arg _ : simpl never.


Notation TargO := (tt : tele_arg TeleO) (only parsing).
Notation TargS a b :=
  ((@TeleArgCons _ (fun x => tele_arg (_ x)) a b) : (tele_arg (TeleS _))) (only parsing).
Coercion tele_arg : tele >-> Sortclass.

Lemma tele_arg_ind (P : forall TT, tele_arg TT -> Prop) :
  P TeleO TargO ->
  (forall T (b : unblock T -> tele) x xs, P (b x) xs -> P (TeleS b) (TargS x xs)) ->
  forall TT (xs : tele_arg TT), P TT xs.
Proof.
  intros H0 HS TT. induction TT as [|T b IH]; simpl.
  - intros []. exact H0.
  - intros [x xs]. apply HS. now auto.
Qed.

Fixpoint tele_app {TT : tele} {U} : (TT -t> U) -> TT -> U :=
  match TT as TT return (TT -t> U) -> TT -> U with
  | TeleO => fun F _ => F
  | TeleS r => fun (F : TeleS r -t> U) '(TeleArgCons x b) =>
      tele_app (F x) b
  end.
Global Arguments tele_app {!_ _} & _ !_ /.

Local Coercion tele_app : tele_fun >-> Funclass.

Lemma tele_arg_inv {TT : tele} (a : tele_arg TT) :
  match TT as TT return tele_arg TT -> Prop with
  | TeleO => fun a => a = TargO
  | TeleS f => fun a => exists x a', a = TargS x a'
  end a.
Proof. destruct TT; destruct a; eauto. Qed.
Lemma tele_arg_O_inv (a : TeleO) : a = TargO.
Proof. exact (tele_arg_inv a). Qed.
Lemma tele_arg_S_inv {X} {f : unblock X -> tele} (a : TeleS f) :
  exists x a', a = TargS x a'.
Proof. exact (tele_arg_inv a). Qed.

Fixpoint tele_map {T U} {TT : tele} : (T -> U) -> (TT -t> T) -> TT -t> U :=
  match TT as TT return (T -> U) -> (TT -t> T) -> TT -t> U with
  | TeleO => fun F : T -> U => F
  | @TeleS X b => fun (F : T -> U) (f : TeleS b -t> T) (x : unblock X) =>
                  tele_map F (f x)
  end.
Global Arguments tele_map {_ _ !_} _ _ /.

Lemma tele_map_app {T U} {TT : tele} (F : T -> U) (t : TT -t> T) (x : TT) :
  (tele_map F t) x = F (t x).
Proof.
  induction TT as [|X f IH]; simpl in x.
  - rewrite (tele_arg_O_inv x). now auto.
  - destruct (tele_arg_S_inv x) as [x' [a' ->]]. simpl.
    rewrite <-IH. now auto.
Qed.

Fixpoint tele_bind {U} {TT : tele} : (TT -> U) -> TT -t> U :=
  match TT as TT return (TT -> U) -> TT -t> U with
  | TeleO => fun F => F tt
  | @TeleS X b => fun (F : TeleS b -> U) (x : unblock X) =>
      tele_bind (fun a => F (TargS x a))
  end.
Global Arguments tele_bind {_ !_} _ /.

Lemma tele_app_bind {U} {TT : tele} (f : TT -> U) x :
  (tele_bind f) x = f x.
Proof.
  induction TT as [|X b IH]; simpl in x.
  - rewrite (tele_arg_O_inv x). now auto.
  - destruct (tele_arg_S_inv x) as [x' [a' ->]]. simpl.
    rewrite IH. now auto.
Qed.

Definition tele_fun_id {TT : tele} : TT -t> TT := tele_bind (fun x => x).

Lemma tele_fun_id_eq {TT : tele} (x : TT) :
  tele_fun_id x = x.
Proof. unfold tele_fun_id. rewrite tele_app_bind. now auto. Qed.

Definition tforall {TT : tele} (Ψ : TT -> Prop) : Prop :=
  tele_fold (fun (T : Type) (b : T -> Prop) => forall x : T, b x) (fun x => x) (tele_bind Ψ).
Global Arguments tforall {!_} _ /.
Definition texist {TT : tele} (Ψ : TT -> Prop) : Prop :=
  tele_fold ex (fun x => x) (tele_bind Ψ).
Global Arguments texist {!_} _ /.

Notation "'forall..' x .. y , P" := (tforall (fun x => .. (tforall (fun y => P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "forall.. x .. y , P") : stdpp_scope.
Notation "'∃..' x .. y , P" := (texist (fun x => .. (texist (fun y => P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "∃.. x .. y , P") : stdpp_scope.

Lemma tforall_forall {TT : tele} (Ψ : TT -> Prop) :
  tforall Ψ <-> (forall x, Ψ x).
Proof.
  symmetry. unfold tforall. induction TT as [|X ft IH].
  - simpl. split.
    + now auto.
    + intros ? p. rewrite (tele_arg_O_inv p). now auto.
  - simpl. split; intros Hx a.
    + rewrite <-IH. now auto.
    + destruct (tele_arg_S_inv a) as [x [pf ->]].
      revert pf. setoid_rewrite IH. now auto.
Qed.

Lemma texist_exist {TT : tele} (Ψ : TT -> Prop) :
  texist Ψ <-> ex Ψ.
Proof.
  symmetry. induction TT as [|X ft IH].
  - simpl. split.
    + intros [p Hp]. rewrite (tele_arg_O_inv p) in Hp. now auto.
    + intros. now exists TargO.
  - simpl. split; intros [p Hp]; revert Hp.
    + destruct (tele_arg_S_inv p) as [x [pf ->]]. intros ?.
      exists x. rewrite <-(IH x (fun a => Ψ (TargS x a))). eauto.
    + rewrite <-(IH p (fun a => Ψ (TargS p a))).
      intros [??]. eauto.
Qed.

Set Printing Implicit.

Monomorphic Universes u u1.
(* Unfortunately reduction happens in the type of the binder. *)
Goal LAZY (TeleS@{u u1} (X:=@block@{Type;_} Type@{u} (1 + 1 = 2)) (fun x : 1 + 1 = 2 => TeleO@{u u1}))
         = TeleS@{u u1} (X:=@block@{Type;_} Type@{u} (1 + 1 = 2)) (fun x :     2 = 2 => TeleO@{u u1}).
Proof. syn_refl. Qed.

End Telescopes.
