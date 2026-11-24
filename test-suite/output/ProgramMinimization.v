(* The universes of a Program declaration are minimized as if its obligations were expanded *)

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.
Set Printing Universes.

Record Rel@{u v} (A : Type@{u}) := { rel : A -> A -> Type@{v}; refl : forall x, rel x x }.
Arguments rel {A}.
Arguments refl {A}.

Record Obj@{u v} := { car : Type@{u}; is_rel : Rel@{u v} car }.

(* The variances are those of the complete term: not those of the type of the obligation,
   [Rel@{u u0} (car X)], merged with them *)
Program Definition obl (X : Obj) : Obj := {| car := car X; is_rel := _ |}.
Next Obligation. intros X; exact (is_rel X). Defined.

Definition obl_expanded (X : Obj) : Obj := {| car := car X; is_rel := is_rel X |}.

About obl.
About obl_expanded.

(* The universe of the relation of the hole is not set to [Set] before the obligation gives the
   relation, which would then force [u = Set], even though the declaration is closed *)
Program Definition prod_obj@{u} (X Y : Obj@{u u}) : Obj@{u u} :=
  {| car := car X * car Y; is_rel := _ |}.
Next Obligation.
  intros X Y.
  exists (fun p q => (rel (is_rel X) (fst p) (fst q) * rel (is_rel Y) (snd p) (snd q))%type).
  intros [x y]; exact (refl (is_rel X) x, refl (is_rel Y) y).
Defined.

Definition prod_obj_expanded@{u} (X Y : Obj@{u u}) : Obj@{u u} :=
  {| car := car X * car Y;
     is_rel := {| rel := fun p q => (rel (is_rel X) (fst p) (fst q) * rel (is_rel Y) (snd p) (snd q))%type;
                  refl := fun p => (refl (is_rel X) (fst p), refl (is_rel Y) (snd p)) |} |}.

About prod_obj.
About prod_obj_expanded.

(* Same without the declaration: the universes of the two arguments stay apart *)
Program Definition prod_obj' (X Y : Obj) : Obj :=
  {| car := car X * car Y; is_rel := _ |}.
Next Obligation.
  intros X Y.
  exists (fun p q => (rel (is_rel X) (fst p) (fst q) * rel (is_rel Y) (snd p) (snd q))%type).
  intros [x y]; exact (refl (is_rel X) x, refl (is_rel Y) y).
Defined.

Definition prod_obj'_arity := prod_obj'@{_ _ _ _}.
Definition prod_obj'_above@{a | Set < a +} (X Y : Obj@{a a}) : Obj@{a a} := prod_obj' X Y.

(* Universes only bounding the arguments of an occurrence of a global ([ext] at [nat]) are set
   to their lower bound, as with the obligation expanded: the first, partial, minimization does
   not substitute others by bounds mentioning them, nor raise them to their upper bounds, and the
   minimization of the obligation leaves them to the one of the definition *)
Definition ext@{a b} {A : Type@{a}} {B : Type@{b}} (f g : A -> B) : Type@{max(a,b)} :=
  forall x, f x = g x.

Program Definition fun_obj : Obj := {| car := nat -> nat; is_rel := {| rel := ext; refl := _ |} |}.
Next Obligation. intros f x; reflexivity. Qed.

Definition fun_obj_expanded : Obj :=
  {| car := nat -> nat; is_rel := {| rel := ext; refl := fun f x => eq_refl |} |}.

About fun_obj.
About fun_obj_expanded.

(* An admitted obligation leaves the universes of its program to the final minimization too:
   its statement keeps the universes of the proved one, [fun_obj_obligation_1] *)
Program Definition fun_obj_adm : Obj :=
  {| car := nat -> nat; is_rel := {| rel := ext; refl := _ |} |}.
Next Obligation. Admitted.

About fun_obj_obligation_1.
About fun_obj_adm_obligation_1.
