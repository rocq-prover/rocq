(* -*- mode: coq; coq-prog-args: ("-noinit" "-indices-matter") -*- *)

(* File reduced by coq-bug-minimizer from original input, then from 839 lines to 73 lines, then from 86 lines to 629 lines, then from 635 lines to 73 lines, then from 86 lines to 677 lines, then from 682 lines to 82 lines, then from 95 lines to 148 lines, then from 154 lines to 82 lines, then from 95 lines to 693 lines, then from 699 lines to 85 lines, then from 98 lines to 137 lines, then from 143 lines to 86 lines, then from 99 lines to 697 lines, then from 703 lines to 150 lines, then from 163 lines to 301 lines, then from 304 lines to 227 lines, then from 240 lines to 282 lines, then from 288 lines to 238 lines, then from 251 lines to 515 lines, then from 521 lines to 268 lines, then from 281 lines to 519 lines, then from 525 lines to 328 lines, then from 341 lines to 418 lines, then from 424 lines to 330 lines, then from 343 lines to 1116 lines, then from 1121 lines to 436 lines, then from 449 lines to 539 lines, then from 545 lines to 443 lines, then from 456 lines to 771 lines, then from 773 lines to 465 lines, then from 479 lines to 464 lines *)
(* coqc version 9.2+alpha compiled with OCaml 4.14.2
   coqtop version runner-wbcqh1i1-project-4504-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 7c064a87db8257) (7c064a87db8257cb769d52951346663e9d8a438e)
   Expected coqc runtime on this file: 0.159 sec *)
Declare Scope type_scope.
Reserved Notation "'exists' x .. y , p"
  (at level 10, x binder, p at level 200,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'").

Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x <-> y" (at level 95, no associativity).
Reserved Notation "~ x" (at level 35, right associativity).

Reserved Notation "x = y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x < y" (at level 70, no associativity).

Reserved Notation "{ x : A  & P }" (at level 0, x at level 99).
Reserved Notation "f == g" (at level 70, no associativity).

Reserved Notation "A <~> B" (at level 85).
Reserved Notation "g 'o' f" (at level 40, left associativity).
Delimit Scope function_scope with function.
Delimit Scope trunc_scope with trunc.

Global Open Scope trunc_scope.
Global Open Scope type_scope.

Declare ML Module "ltac_plugin:coq-core.plugins.ltac".

Declare ML Module "number_string_notation_plugin:coq-core.plugins.number_string_notation".

Global Set Default Proof Mode "Classic".

Global Set Universe Polymorphism.

Global Unset Strict Universe Declaration.
Create HintDb typeclass_instances discriminated.

Notation "A -> B" := (forall (_ : A), B) : type_scope.

Inductive option (A : Type) : Type :=
| Some : A -> option A
| None : option A.

Arguments Some {A} a.
Arguments None {A}.

Register option as core.option.type.

Record prod (A B : Type) := pair { fst : A ; snd : B }.

Definition Relation (A : Type) := A -> A -> Type.

Class Reflexive {A} (R : Relation A) :=
  reflexivity : forall x : A, R x x.

Class Transitive {A} (R : Relation A) :=
  transitivity : forall x y z, R x y -> R y z -> R x z.

Notation Type0 := Set.

Notation idmap := (fun x => x).

Record sig {A} (P : A -> Type) := exist {
  proj1 : A ;
  proj2 : P proj1 ;
}.
Notation "'exists' x .. y , p" := (sig (fun x => .. (sig (fun y => p)) ..)) : type_scope.
Notation "{ x : A  & P }" := (sig (fun x:A => P)) : type_scope.

Notation compose := (fun g f x => g (f x)).

Notation "g 'o' f" := (compose g%function f%function) : function_scope.

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.
Definition ap {A B : Type} (f : A -> B) {x y : A} (p : x = y) : f x = f y.
Admitted.

Definition pointwise_paths A (P : A -> Type) (f g : forall x, P x)
  := forall x, f x = g x.

Global Arguments pointwise_paths {A}%_type_scope {P} (f g)%_function_scope.

Notation "f == g" := (pointwise_paths f g) : type_scope.

Class IsEquiv {A B : Type} (f : A -> B) := {
  equiv_inv : B -> A ;
  eisretr : f o equiv_inv == idmap ;
  eissect : equiv_inv o f == idmap ;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x) ;
}.

Record Equiv A B := {
  equiv_fun : A -> B ;
  equiv_isequiv :: IsEquiv equiv_fun
}.

Notation "A <~> B" := (Equiv A B) : type_scope.

Inductive trunc_index : Type0 :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

Notation "n .+1" := (trunc_S n) : trunc_scope.
Notation "n .+2" := (n.+1.+1)%trunc : trunc_scope.

Inductive IsTrunc_internal (A : Type@{u}) : trunc_index -> Type@{u} :=
| Build_Contr : forall (center : A) (contr : forall y, center = y), IsTrunc_internal A minus_two
| istrunc_S : forall {n:trunc_index}, (forall x y:A, IsTrunc_internal (x = y) n) -> IsTrunc_internal A (trunc_S n).

Existing Class IsTrunc_internal.

Notation IsTrunc n A := (IsTrunc_internal A n).
Notation IsHProp A := (IsTrunc minus_two.+1 A).
Notation IsHSet A := (IsTrunc minus_two.+2 A).

Notation is_mere_relation A R := (forall (x y : A), IsHProp (R x y)).

Inductive nat : Type0 :=
| O : nat
| S : nat -> nat.
Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.

Inductive Empty : Type0 := .

Definition not (A : Type) := A -> Empty.
Notation "~ x" := (not x) : type_scope.
Definition complement {A} (R : Relation A) : Relation A.
exact (fun x y => ~ (R x y)).
Defined.

Class Irreflexive {A} (R : Relation A) :=
  irreflexivity : Reflexive (complement R).

Monomorphic Axiom PropResizing : Type0.
Existing Class PropResizing.

Definition iff (A B : Type) := prod (A -> B) (B -> A).

Notation "A <-> B" := (iff A B) : type_scope.
Module Export Decimal.

Inductive uint : Type0 :=
 | Nil
 | D0 (_:uint)
 | D1 (_:uint)
 | D2 (_:uint)
 | D3 (_:uint)
 | D4 (_:uint)
 | D5 (_:uint)
 | D6 (_:uint)
 | D7 (_:uint)
 | D8 (_:uint)
 | D9 (_:uint).

Notation zero := (D0 Nil).

Variant int : Type0 := Pos (d:uint) | Neg (d:uint).

Variant decimal : Type0 :=
 | Decimal (i:int) (f:uint)
 | DecimalExp (i:int) (f:uint) (e:int).

Register uint as num.uint.type.
Register int as num.int.type.
Register decimal as num.decimal.type.

Fixpoint revapp (d d' : uint) :=
  match d with
  | Nil => d'
  | D0 d => revapp d (D0 d')
  | D1 d => revapp d (D1 d')
  | D2 d => revapp d (D2 d')
  | D3 d => revapp d (D3 d')
  | D4 d => revapp d (D4 d')
  | D5 d => revapp d (D5 d')
  | D6 d => revapp d (D6 d')
  | D7 d => revapp d (D7 d')
  | D8 d => revapp d (D8 d')
  | D9 d => revapp d (D9 d')
  end.

Definition rev d := revapp d Nil.

Module Export Little.

Fixpoint succ d :=
  match d with
  | Nil => D1 Nil
  | D0 d => D1 d
  | D1 d => D2 d
  | D2 d => D3 d
  | D3 d => D4 d
  | D4 d => D5 d
  | D5 d => D6 d
  | D6 d => D7 d
  | D7 d => D8 d
  | D8 d => D9 d
  | D9 d => D0 (succ d)
  end.
End Little.
End Decimal.

Module Export Hexadecimal.

Inductive uint : Type0 :=
 | Nil
 | D0 (_:uint)
 | D1 (_:uint)
 | D2 (_:uint)
 | D3 (_:uint)
 | D4 (_:uint)
 | D5 (_:uint)
 | D6 (_:uint)
 | D7 (_:uint)
 | D8 (_:uint)
 | D9 (_:uint)
 | Da (_:uint)
 | Db (_:uint)
 | Dc (_:uint)
 | Dd (_:uint)
 | De (_:uint)
 | Df (_:uint).

Variant int : Type0 := Pos (d:uint) | Neg (d:uint).

Variant hexadecimal : Type0 :=
 | Hexadecimal (i:int) (f:uint)
 | HexadecimalExp (i:int) (f:uint) (e:Decimal.int).

Register uint as num.hexadecimal_uint.type.
Register int as num.hexadecimal_int.type.
Register hexadecimal as num.hexadecimal.type.

End Hexadecimal.

Module Export Numeral.

Variant uint : Type0 := UIntDec (u:Decimal.uint) | UIntHex (u:Hexadecimal.uint).

Variant int : Type0 := IntDec (i:Decimal.int) | IntHex (i:Hexadecimal.int).

Variant numeral : Type0 := Dec (d:Decimal.decimal) | Hex (h:Hexadecimal.hexadecimal).

Register uint as num.num_uint.type.
Register int as num.num_int.type.
Register numeral as num.number.type.
End Numeral.

Module Export Nat.

Fixpoint tail_add n m :=
  match n with
    | O => m
    | S n => tail_add n (S m)
  end.

Fixpoint tail_addmul r n m :=
  match n with
    | O => r
    | S n => tail_addmul (tail_add m r) n m
  end.

Definition tail_mul n m := tail_addmul O n m.

Local Notation ten := (S (S (S (S (S (S (S (S (S (S O)))))))))).

Fixpoint of_uint_acc (d:Decimal.uint)(acc:nat) :=
  match d with
  | Decimal.Nil => acc
  | Decimal.D0 d => of_uint_acc d (tail_mul ten acc)
  | Decimal.D1 d => of_uint_acc d (S (tail_mul ten acc))
  | Decimal.D2 d => of_uint_acc d (S (S (tail_mul ten acc)))
  | Decimal.D3 d => of_uint_acc d (S (S (S (tail_mul ten acc))))
  | Decimal.D4 d => of_uint_acc d (S (S (S (S (tail_mul ten acc)))))
  | Decimal.D5 d => of_uint_acc d (S (S (S (S (S (tail_mul ten acc))))))
  | Decimal.D6 d => of_uint_acc d (S (S (S (S (S (S (tail_mul ten acc)))))))
  | Decimal.D7 d => of_uint_acc d (S (S (S (S (S (S (S (tail_mul ten acc))))))))
  | Decimal.D8 d => of_uint_acc d (S (S (S (S (S (S (S (S (tail_mul ten acc)))))))))
  | Decimal.D9 d => of_uint_acc d (S (S (S (S (S (S (S (S (S (tail_mul ten acc))))))))))
  end.

Definition of_uint (d:Decimal.uint) := of_uint_acc d O.

Local Notation sixteen := (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))).

Fixpoint of_hex_uint_acc (d:Hexadecimal.uint)(acc:nat) :=
  match d with
  | Hexadecimal.Nil => acc
  | Hexadecimal.D0 d => of_hex_uint_acc d (tail_mul sixteen acc)
  | Hexadecimal.D1 d => of_hex_uint_acc d (S (tail_mul sixteen acc))
  | Hexadecimal.D2 d => of_hex_uint_acc d (S (S (tail_mul sixteen acc)))
  | Hexadecimal.D3 d => of_hex_uint_acc d (S (S (S (tail_mul sixteen acc))))
  | Hexadecimal.D4 d => of_hex_uint_acc d (S (S (S (S (tail_mul sixteen acc)))))
  | Hexadecimal.D5 d => of_hex_uint_acc d (S (S (S (S (S (tail_mul sixteen acc))))))
  | Hexadecimal.D6 d => of_hex_uint_acc d (S (S (S (S (S (S (tail_mul sixteen acc)))))))
  | Hexadecimal.D7 d => of_hex_uint_acc d (S (S (S (S (S (S (S (tail_mul sixteen acc))))))))
  | Hexadecimal.D8 d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (tail_mul sixteen acc)))))))))
  | Hexadecimal.D9 d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc))))))))))
  | Hexadecimal.Da d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc)))))))))))
  | Hexadecimal.Db d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc))))))))))))
  | Hexadecimal.Dc d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc)))))))))))))
  | Hexadecimal.Dd d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc))))))))))))))
  | Hexadecimal.De d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc)))))))))))))))
  | Hexadecimal.Df d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc))))))))))))))))
  end.

Definition of_hex_uint (d:Hexadecimal.uint) := of_hex_uint_acc d O.

Definition of_num_uint (d:Numeral.uint) :=
  match d with
  | Numeral.UIntDec d => of_uint d
  | Numeral.UIntHex d => of_hex_uint d
  end.

Fixpoint to_little_uint n acc :=
  match n with
  | O => acc
  | S n => to_little_uint n (Decimal.Little.succ acc)
  end.

Definition to_uint n :=
  Decimal.rev (to_little_uint n Decimal.zero).

Definition to_num_uint n := Numeral.UIntDec (to_uint n).

End Nat.

Number Notation nat of_num_uint to_num_uint (abstract after 5001) : nat_scope.
Fixpoint trunc_index_inc@{} (k : trunc_index) (n : nat)
  : trunc_index.
exact (match n with
      | O => k
      | S m => (trunc_index_inc k m).+1
    end).
Defined.
Definition nat_to_trunc_index@{} (n : nat) : trunc_index.
exact ((trunc_index_inc minus_two n).+2).
Defined.
Definition int_to_trunc_index@{} (v : Decimal.int) : option trunc_index.
exact (match v with
     | Decimal.Pos d => Some (nat_to_trunc_index (Nat.of_uint d))
     | Decimal.Neg d => match Nat.of_uint d with
                        | 2%nat => Some minus_two
                        | 1%nat => Some (minus_two.+1)
                        | 0%nat => Some (minus_two.+2)
                        | _ => None
                        end
     end).
Defined.
Definition num_int_to_trunc_index@{} (v : Numeral.int) : option trunc_index.
exact (match v with
  | Numeral.IntDec v => int_to_trunc_index v
  | Numeral.IntHex _ => None
  end).
Defined.

Fixpoint trunc_index_to_little_uint@{} n acc :=
  match n with
  | minus_two => acc
  | minus_two.+1 => acc
  | minus_two.+2 => acc
  | trunc_S n => trunc_index_to_little_uint n (Decimal.Little.succ acc)
  end.

Definition trunc_index_to_int@{} n :=
  match n with
  | minus_two => Decimal.Neg (Nat.to_uint 2)
  | minus_two.+1 => Decimal.Neg (Nat.to_uint 1)
  | n => Decimal.Pos (Decimal.rev (trunc_index_to_little_uint n Decimal.zero))
  end.

Definition trunc_index_to_num_int@{} n :=
  Numeral.IntDec (trunc_index_to_int n).

Number Notation trunc_index num_int_to_trunc_index trunc_index_to_num_int
  : trunc_scope.

Record TruncType (n : trunc_index) := {
  trunctype_type : Type ;
  trunctype_istrunc :: IsTrunc n trunctype_type
}.

Arguments Build_TruncType _ _ {_}.

Coercion trunctype_type : TruncType >-> Sortclass.

Notation "n -Type" := (TruncType n) : type_scope.
Notation HSet := 0-Type.
Notation Build_HSet := (Build_TruncType 0).

Monomorphic Axiom Univalence : Type0.
Existing Class Univalence.

Declare Scope mc_scope.

Open Scope mc_scope.
Class Lt A := lt: Relation A.

Infix "<" := lt : mc_scope.
Notation "(<)" := lt (only parsing) : mc_scope.

Inductive Accessible {A} (R : Lt A) (a : A) :=
  acc : (forall b, b < a -> Accessible R b) -> Accessible R a.

Class WellFounded {A} (R : Relation A) :=
  well_foundedness : forall a : A, Accessible R a.

Class Extensional {A} (R : Lt A) :=
  extensionality : forall a b : A, (forall c : A, c < a <-> c < b) -> a = b.

Class IsOrdinal@{carrier relation} (A : Type@{carrier}) (R : Relation@{carrier relation} A) := {
  ordinal_is_hset :: IsHSet A ;
  ordinal_relation_is_mere :: is_mere_relation A R ;
  ordinal_extensionality :: Extensional R ;
  ordinal_well_foundedness :: WellFounded R ;
  ordinal_transitivity :: Transitive R ;
}.

Record Ordinal@{carrier relation +} :=
  { ordinal_carrier : Type@{carrier}
    ; ordinal_relation :: Lt@{carrier relation} ordinal_carrier
    ; ordinal_property :: IsOrdinal@{carrier relation} ordinal_carrier (<)
  }.
Coercion ordinal_as_hset (A : Ordinal) : HSet.
exact (Build_HSet (ordinal_carrier A)).
Defined.

Instance irreflexive_ordinal_relation A R
  : IsOrdinal A R -> Irreflexive R.
Proof.
  intros is_ordinal a H. Check (well_foundedness a).
  induction (well_foundedness a) as [a _ IH].
  apply (IH a); assumption.
Qed.

Definition TypeWithRelation
  := { A : Type & Relation A }.
Coercion ordinal_as_type_with_relation (A : Ordinal) : TypeWithRelation.
Admitted.
Definition Isomorphism : TypeWithRelation -> TypeWithRelation -> Type.
Admitted.

Definition equiv_path_Ordinal `{Univalence} (A B : Ordinal)
  : Isomorphism A B <~> A = B.
Admitted.

Definition initial_segment `{PropResizing}
           {A : Type} {R : Lt A} `{IsOrdinal A R} (a : A)
  : Ordinal.
Admitted.

Declare Scope Ordinals.
Open Scope Ordinals.

Notation "↓ a" := (initial_segment a) (at level 4, format "↓ a") : Ordinals.
Instance lt_Ordinal@{carrier relation +} `{PropResizing}
  : Lt Ordinal@{carrier relation}.
exact (fun A B => exists b : B, A = ↓b).
Defined.

Instance Ordinal_is_ordinal `{PropResizing} `{Univalence}
  : IsOrdinal Ordinal (<).
Admitted.

Lemma ordinal_initial `{PropResizing} `{Univalence} (O : Ordinal) (a : O)
  (p : O = ↓a)
  (HO : O < O)
  : Empty.
Proof.
  exact (irreflexive_ordinal_relation _ _ _ _ HO).
Qed.
