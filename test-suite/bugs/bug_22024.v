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
