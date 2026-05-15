(* Regression tests for cbn refolding after iota.
   The expected output is the behavior of master: transparent aliases
   must not be refolded once their arguments have reduced enough to
   allow the alias itself to compute. *)


Set Printing Width 200.
Require Import PrimString.
Open Scope pstring_scope.

Definition id_nat (x : nat) := x.
Definition id_Type (A : Type) := A.
Definition id_Prop (P : Prop) := P.
Definition id_fun (f : nat -> nat) := f.
Definition id_pair (p : nat * nat) := p.
Definition fst_nat (x y : nat) := x.
Definition snd_nat (x y : nat) := y.
Definition third_nat (x y z : nat) := z.
Definition id_poly {A : Type} (x : A) := x.
Definition ret_cast (x : nat) : nat := (x : nat).

Definition pcase (n : nat) := match n with O => O | S p => p end.
Definition pcase2 (n : nat) := match n with O => O | S p => match p with O => O | S q => q end end.

Inductive box := Box : nat -> box | Empty : box.
Definition id_box (b : box) := b.

Record R := mkR { ra : nat; rb : nat }.
Definition id_R (r : R) := r.

Set Primitive Projections.
Record PR := mkPR { pra : nat; prb : nat }.
Unset Primitive Projections.
Definition id_PR (r : PR) := r.

Definition set := { t : nat | True }.
Definition set0 : set := exist _ O I.
Definition setS (n : nat) : set := exist _ (S n) I.
Definition set_difference : set -> set -> set :=
  fun X Y => let (t1, _) := X in let (t2, _) := Y in exist _ t1 I.
Definition difference_direct {A} (D : A -> A -> A) : A -> A -> A := D.
Definition difference_cast {A} (D : A -> A -> A) : A -> A -> A := (D : A -> A -> A).

Class Difference (A : Type) := difference_cls : A -> A -> A.
Definition set_difference_cls : Difference set := set_difference.

Check "** direct closed aliases".
Eval cbn in id_nat (if true then O else S O).
Eval cbn in id_nat (match S O with O => O | S p => p end).
Eval cbn in @difference_cls set set_difference_cls set0 (setS O).

Check "** aliases over reduced iota arguments".
Check "alias_id_nat_inline_match_S".
Eval cbn in (fun x : nat => id_nat ((match S x with O => O | S p => p end))).
Check "alias_id_nat_inline_if_true".
Eval cbn in (fun x : nat => id_nat ((if true then S x else O))).
Check "alias_id_nat_def_match_S".
Eval cbn in (fun x : nat => id_nat (pcase (S x))).
Check "alias_id_nat_def_match_SS".
Eval cbn in (fun x : nat => id_nat (pcase2 (S (S x)))).
Check "alias_id_nat_beta_then_iota".
Eval cbn in (fun x : nat => id_nat (((fun y : nat => pcase (S y)) x))).
Check "alias_fst_nat_inline_match_S".
Eval cbn in (fun x : nat => fst_nat ((match S x with O => O | S p => p end)) O).
Check "alias_fst_nat_inline_if_true".
Eval cbn in (fun x : nat => fst_nat ((if true then S x else O)) O).
Check "alias_fst_nat_def_match_S".
Eval cbn in (fun x : nat => fst_nat (pcase (S x)) O).
Check "alias_fst_nat_def_match_SS".
Eval cbn in (fun x : nat => fst_nat (pcase2 (S (S x))) O).
Check "alias_fst_nat_beta_then_iota".
Eval cbn in (fun x : nat => fst_nat (((fun y : nat => pcase (S y)) x)) O).
Check "alias_snd_nat_inline_match_S".
Eval cbn in (fun x : nat => snd_nat O ((match S x with O => O | S p => p end))).
Check "alias_snd_nat_inline_if_true".
Eval cbn in (fun x : nat => snd_nat O ((if true then S x else O))).
Check "alias_snd_nat_def_match_S".
Eval cbn in (fun x : nat => snd_nat O (pcase (S x))).
Check "alias_snd_nat_def_match_SS".
Eval cbn in (fun x : nat => snd_nat O (pcase2 (S (S x)))).
Check "alias_snd_nat_beta_then_iota".
Eval cbn in (fun x : nat => snd_nat O (((fun y : nat => pcase (S y)) x))).
Check "alias_third_nat_inline_match_S".
Eval cbn in (fun x : nat => third_nat O O ((match S x with O => O | S p => p end))).
Check "alias_third_nat_inline_if_true".
Eval cbn in (fun x : nat => third_nat O O ((if true then S x else O))).
Check "alias_third_nat_def_match_S".
Eval cbn in (fun x : nat => third_nat O O (pcase (S x))).
Check "alias_third_nat_def_match_SS".
Eval cbn in (fun x : nat => third_nat O O (pcase2 (S (S x)))).
Check "alias_third_nat_beta_then_iota".
Eval cbn in (fun x : nat => third_nat O O (((fun y : nat => pcase (S y)) x))).
Check "alias_id_poly_nat_inline_match_S".
Eval cbn in (fun x : nat => @id_poly nat ((match S x with O => O | S p => p end))).
Check "alias_id_poly_nat_inline_if_true".
Eval cbn in (fun x : nat => @id_poly nat ((if true then S x else O))).
Check "alias_id_poly_nat_def_match_S".
Eval cbn in (fun x : nat => @id_poly nat (pcase (S x))).
Check "alias_id_poly_nat_def_match_SS".
Eval cbn in (fun x : nat => @id_poly nat (pcase2 (S (S x)))).
Check "alias_id_poly_nat_beta_then_iota".
Eval cbn in (fun x : nat => @id_poly nat (((fun y : nat => pcase (S y)) x))).
Check "alias_ret_cast_inline_match_S".
Eval cbn in (fun x : nat => ret_cast ((match S x with O => O | S p => p end))).
Check "alias_ret_cast_inline_if_true".
Eval cbn in (fun x : nat => ret_cast ((if true then S x else O))).
Check "alias_ret_cast_def_match_S".
Eval cbn in (fun x : nat => ret_cast (pcase (S x))).
Check "alias_ret_cast_def_match_SS".
Eval cbn in (fun x : nat => ret_cast (pcase2 (S (S x)))).
Check "alias_ret_cast_beta_then_iota".
Eval cbn in (fun x : nat => ret_cast (((fun y : nat => pcase (S y)) x))).
Check "selected_under_pair".
Eval cbn in (fun x : nat => id_pair (match true with true => (x,O) | false => (O,x) end)).
Check "sort_id_Type_if_true".
Eval cbn in id_Type (if true then nat else bool).
Check "sort_id_Prop_if_true".
Eval cbn in id_Prop (if true then True else False).
Check "sort_id_Prop_under_fun".
Eval cbn in (fun P : Prop => id_Prop (if true then P else False)).
Check "fun_id_if_true".
Eval cbn in id_fun (if true then S else fun x => x).
Check "fun_id_if_true_applied".
Eval cbn in (fun x : nat => id_fun (if true then S else fun x => x) x).
Check "record_id_R_if_true".
Eval cbn in (fun x : nat => id_R (if true then mkR x O else mkR O x)).
Check "prim_record_id_PR_if_true".
Eval cbn in (fun x : nat => id_PR (if true then mkPR x O else mkPR O x)).
Check "box_id_if_true".
Eval cbn in id_box (if true then Box O else Empty).
Check "set_id_poly_if_true".
Eval cbn in @id_poly set (if true then set0 else setS O).
Check "set_difference_direct".
Eval cbn in (fun y : set => @difference_direct set set_difference set0 y).
Check "set_difference_cast".
Eval cbn in (fun y : set => @difference_cast set set_difference set0 y).
Check "set_difference_class".
Eval cbn in (fun y : set => @difference_cls set set_difference_cls set0 y).
Check "set_difference_direct_both_known".
Eval cbn in @difference_direct set set_difference set0 (setS O).
Check "set_difference_class_both_known".
Eval cbn in @difference_cls set set_difference_cls set0 (setS O).
