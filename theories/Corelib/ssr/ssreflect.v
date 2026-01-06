(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export ssreflect_rw.
Declare ML Module "rocq-runtime.plugins.ssreflect_rewrite".
(** Signal that we have ssreflect version of rewrite (meaning
 "rewrite a" must be printed "rewrite -> a" for compatibility). **)
#[export] Set SSRRewrite Loaded.

(** Reserve notations that are introduced in this file. **)
Reserved Notation "[ 'the' sT 'of' v 'by' f ]" (at level 0,
  format "[ 'the'  sT  'of'  v  'by'  f ]").

Reserved Notation "[ 'the' sT 'of' v ]" (at level 0,
  format "[ 'the'  sT  'of'  v ]").
Reserved Notation "{ 'type' 'of' c 'for' s }" (at level 0,
  format "{ 'type'  'of'  c  'for'  s }").

Reserved Notation "[ 'unlockable' 'of' C ]" (at level 0,
  format "[ 'unlockable'  'of'  C ]").

Import TheCanonical. (* Note: no export. *)

Local Arguments get_by _%_type_scope _%_type_scope _ _ _ _.

Notation "[ 'the' sT 'of' v 'by' f ]" :=
  (@get_by _ sT f _ _ ((fun v' (s : sT) => Put v' (f s) s) v _))
  (only parsing) : form_scope.

Notation "[ 'the' sT 'of' v ]" := (get ((fun s : sT => Put v (*coerce*) s s) _))
  (only parsing) : form_scope.

(**
 The following are "format only" versions of the above notations.
 We need to do this to prevent the formatter from being be thrown off by
 application collapsing, coercion insertion and beta reduction in the right
 hand side of the notations above.                                           **)

Notation "[ 'the' sT 'of' v 'by' f ]" := (@get_by _ sT f v _ _)
  (only printing) : form_scope.

Notation "[ 'the' sT 'of' v ]" := (@get _ sT v _ _)
  (only printing) : form_scope.

(**
 We would like to recognize
Notation " #[# 'the' sT 'of' v : 'Type' #]#" := (@get Type sT v _ _)
  (at level 0, format " #[# 'the'  sT   'of'  v  :  'Type' #]#") : form_scope.
 **)

Notation "[ 'unlockable' 'of' C ]" :=
  (@Unlockable _ _ C (unlock _)) : form_scope.

(** Save primitive notation that will be overloaded. **)
Local Abbreviation RocqGenericIf c vT vF :=
  (if c then vT else vF) (only parsing).
Local Abbreviation RocqGenericDependentIf c x R vT vF :=
  (if c as x return R then vT else vF) (only parsing).

(** Reserve notations that are introduced in this file. **)
Reserved Notation "'if' c 'then' vT 'else' vF" (at level 200,
  c, vT, vF at level 200).
Reserved Notation "'if' c 'return' R 'then' vT 'else' vF" (at level 200,
  c, R, vT, vF at level 200).
Reserved Notation "'if' c 'as' x 'return' R 'then' vT 'else' vF" (at level 200,
  c, R, vT, vF at level 200, x name).

(**
 Make the general "if" into a notation, so that we can override it below.
 The notations are "only parsing" because the Rocq decompiler will not
 recognize the expansion of the boolean if; using the default printer
 avoids a spurious trailing %%GEN_IF. **)

Declare Scope general_if_scope.
Delimit Scope general_if_scope with GEN_IF.

Notation "'if' c 'then' vT 'else' vF" :=
  (RocqGenericIf c vT vF) (only parsing) : general_if_scope.

Notation "'if' c 'return' R 'then' vT 'else' vF" :=
  (RocqGenericDependentIf c c R vT vF) (only parsing) : general_if_scope.

Notation "'if' c 'as' x 'return' R 'then' vT 'else' vF" :=
  (RocqGenericDependentIf c x R vT vF) (only parsing) : general_if_scope.

(**  Force boolean interpretation of simple if expressions.  **)

Declare Scope boolean_if_scope.
Delimit Scope boolean_if_scope with BOOL_IF.

Notation "'if' c 'return' R 'then' vT 'else' vF" :=
  (if c is true as c in bool return R then vT else vF) : boolean_if_scope.

Notation "'if' c 'then' vT 'else' vF" :=
  (if c%bool is true as _ in bool return _ then vT else vF) : boolean_if_scope.

Notation "'if' c 'as' x 'return' R 'then' vT 'else' vF" :=
  (if c%bool is true as x in bool return R then vT else vF) : boolean_if_scope.

Open Scope boolean_if_scope.

(* This abbreviation is only parsing in Prelude *)
Abbreviation unkeyed x := (let flex := x in flex).

Abbreviation phant := ssreflect_rw.phant.
Abbreviation Phant := ssreflect_rw.Phant.
Abbreviation phantom := ssreflect_rw.phantom.
Abbreviation Phantom := ssreflect_rw.Phantom.
