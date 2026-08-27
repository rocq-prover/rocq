(** Guard condition was inconsistent with Univalence and nested inductive types
    due to an insufficient restriction of PropExt fix
*)

Inductive Box A :=
| box : A -> Box A
| wrap : Box A -> Box A.

Arguments box {_}.
Arguments wrap {_}.

Inductive Boxed :=
| nobox : Boxed
| boxed : Box Boxed -> Boxed.

Fail Fixpoint weird_subterm (e : Boxed = Boxed :> Type) (x : Box Boxed) :=
  match x with
  | box x => x
  | wrap y => weird_subterm e (match e in _ = Y return Box Y with eq_refl => y end)
  end.

(* The same issue arises with beta-iota cuts *)
Fail Fixpoint weird_beta (e : Boxed = Boxed :> Type) (x : Box Boxed) :=
  match x with
  | box x => x
  | wrap y => match e in _ = Y return Box Y -> Boxed with
                eq_refl => fun y => weird_beta e y
              end y
  end.

(* Variant where the fixpoint itself goes through the stack *)
Fail Fixpoint weird_stack (f : Boxed -> Boxed) (e : Boxed = Boxed :> Type) (x : Box Boxed) :=
  match x with
  | box x => f x
  | wrap y => (match e in _ = Y return Box Y -> Boxed with
               | eq_refl => weird_stack f e
               end) y
  end.

(* The abstracted variable may also be used indirectly, through a variable
   bound inside the return clause *)
Fail Fixpoint weird_indirect (e : Boxed = Boxed :> Type) (x : Box Boxed) :=
  match x with
  | box x => x
  | wrap y =>
    weird_indirect e
      (match e in _ = Y return forall Z, Z = Y -> Box Z with
       | eq_refl => fun Z e' => match e' in _ = W return Box W -> Box Z with
                                | eq_refl => fun y => y
                                end y
       end Boxed e)
  end.


Inductive BoolBox A :=
| boolbox : A -> BoolBox A
| boolwrap : bool * BoolBox A -> BoolBox A.

Arguments boolbox {_}.
Arguments boolwrap {_}.

Definition BoolBox' := BoolBox.

Fail Fixpoint weird_beta_alias (e : Boxed = Boxed :> Type) (x : BoolBox Boxed) :=
  match x with
  | boolbox x => x
  | boolwrap y => match e in _ = Y return bool * BoolBox' Y -> Boxed with
                eq_refl => fun z => weird_beta_alias e (snd z)
              end y
  end.

(* Aliases must also be seen through in the return type itself *)
Definition Box' := Box.

Fail Fixpoint weird_alias (e : Boxed = Boxed :> Type) (x : Box Boxed) :=
  match x with
  | box x => x
  | wrap y => weird_alias e (match e in _ = Y return Box' Y with eq_refl => y end)
  end.

(** Transport a uniform parameter is forbidden even if it is not an arity
    due to the dynamic encoding of nesting that could transport a true to
    false, then reducing away and changing the type of nestable parameter
*)
Inductive T (A : unit) := node (x : T A) with U (A : unit) := .

Fail Fixpoint F (e : tt = tt) (x : T tt) : False :=
  match x with
  | node _ x =>
    F e match e in _ = t return T t with eq_refl => x end
  end.


(** The transported occurrence can be hidden as a (possibly eta-expanded)
    parameter of another container, so occurrences of the structural
    argument's inductive must be sufficiently applied, to the very same
    uniform parameters *)
Module NestedContainer.

Unset Elimination Schemes.
Set Primitive Projections.

Record Pain (F : Type -> Type) (A : Type) := pain { unpain : F A }.
Arguments pain {F A}.
Arguments unpain {F A}.

Inductive RBox A := rbox (x : A) | rwrap (y : Pain RBox A).
Arguments rbox {A}.
Arguments rwrap {A}.

Fail Fixpoint weird_nested (f : Boxed -> Boxed) (e : Boxed = Boxed :> Type)
  (x : RBox Boxed) {struct x} :=
  match x with
  | rbox x => f x
  | rwrap y =>
    weird_nested f e
      (unpain (match e in _ = Y return Pain RBox Y with eq_refl => y end))
  end.

Fail Fixpoint weird_nested_eta (f : Boxed -> Boxed) (e : Boxed = Boxed :> Type)
  (x : RBox Boxed) {struct x} :=
  match x with
  | rbox x => f x
  | rwrap y =>
    weird_nested_eta f e
      (unpain (match e in _ = Y return Pain (fun T => RBox T) Y with eq_refl => y end))
  end.

End NestedContainer.

(** However, transports on indices is accepted *)
Inductive I : nat -> Type :=
| C0 : { n : nat & (False * I n)} -> I 0.

Fixpoint foo n (x : I n) : nat :=
  match x with
  | C0 p => foo (projT1 p) (snd (projT2 p))
  end.

Fixpoint foo' {n} (x : I n) {struct x} : nat :=
  match x with
  | C0 p => foo' (
      match (
        match p return False * I (projT1 p) with
        | existT _ _ h => h
        end
      )
      return I (projT1 p) with
      | (_,b) => b
      end
    )
  end.

(** The restriction must not reject guarded cofixpoints: the cofix binders are
    not pushed to the environment during the guard traversal, which used to
    shift the comparison of uniform parameters by the number of cofix binders.
    This was latent on section variables (unaffected by lifting) and wrongly
    triggered once the parameters are Rels, e.g. after discharge, in which
    case only rocqchk would re-check (and reject) the discharged cofix. *)
CoInductive stream (A : Type) : Type := scons : A -> stream A -> stream A.

Definition guarded_loop : forall (A : Type) (a : A), (bool = bool) -> stream A :=
  fun A a => cofix IH (e : bool = bool) : stream A :=
    match e in _ = b return (b -> stream A) with
    | eq_refl => fun _ => scons A a (IH e)
    end true.

(* Discharged variant, as found in stdpp's [ex_loop_tc]: accepted in the
   section on Var parameters, and re-checked on Rel parameters by rocqchk
   after discharge. *)
Section CofixDischarge.
  Context {A : Type} (R : A -> A -> Prop).

  CoInductive ex_loop : A -> Prop :=
  | ex_loop_do_step x y : R x y -> ex_loop y -> ex_loop x.
End CofixDischarge.

Section CofixDischargeUse.
  Context {A : Type} (R : A -> A -> Prop).

  Lemma ex_loop_weaken (R' : A -> A -> Prop)
    (HR : forall x y, R x y -> R' x y) x : ex_loop R x -> ex_loop R' x.
  Proof.
    revert x; cofix IH.
    intros x H.
    destruct H as [x y Hstep Hloop].
    apply (@ex_loop_do_step A R' x y).
    - apply HR, Hstep.
    - apply IH, Hloop.
  Qed.
End CofixDischargeUse.

(** The comparison of uniform parameters up to conversion may involve
    universes not yet declared in the kernel environment when guard checking
    is called during elaboration (e.g. through [Pretyping.search_guard]),
    which used to raise an "undefined universe" anomaly. The environment must
    be equipped with the universes of the evar map. *)
Fixpoint arrows (rep : Type) (dom : list Type) : Type :=
  match dom with
  | nil => rep
  | cons d dom' => d -> arrows rep dom'
  end.

Fixpoint from_arrows {rep : Type} {dom : list Type}
  (c : arrows rep dom) (r : rep) {struct dom} : Prop :=
  match dom return arrows rep dom -> rep -> Prop with
  | nil => fun c r => True
  | cons D dom' => fun c r => exists d : D, from_arrows (c d) r
  end c r.
