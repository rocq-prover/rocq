(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Ltac2 Require Import Init Std.
From Ltac2 Require List.

(** The name of a module or module type. It may be a functor. It may also be currently open. *)
Ltac2 Type t.

Module Export Notations.
  (** Use as e.g. [module:(Ltac2.Module.Notations)]. *)
  Ltac2 Notation "module:(" x(module) ")" : 0 := x.
End Notations.
(* XXX add dynamic lookup (like Env.get)? *)

(** Test equality of module names. *)
Ltac2 @external equal : t -> t -> bool
  := "rocq-runtime.plugins.ltac2" "module_equal".

(** Print a module name. *)
Ltac2 @external to_message : t -> message
  := "rocq-runtime.plugins.ltac2" "module_to_message".

(** This returns [true] for both module types and module type functors. *)
Ltac2 @external is_modtype : t -> bool
  := "rocq-runtime.plugins.ltac2" "module_is_modtype".

(** This returns [true] for both module functors and module type functors. *)
Ltac2 @external is_functor : t -> bool
  := "rocq-runtime.plugins.ltac2" "module_is_functor".

(** This returns [true] for modules which are arguments of a currently open functor
    ([false] for submodules of bound modules). *)
Ltac2 @external is_bound_module : t -> bool
  := "rocq-runtime.plugins.ltac2" "module_is_bound_module".

(** This returns [true] for modules which are libraries (i.e. files). *)
Ltac2 @external is_library : t -> bool
  := "rocq-runtime.plugins.ltac2" "module_is_library".

(** This returns [true] if the argument refers to a currently open
    interactive module (or module type or functor). *)
Ltac2 @external is_open : t -> bool
  := "rocq-runtime.plugins.ltac2" "module_is_open".

(** Return the parent module, ie [A] for [A.B].
    Toplevel modules (libraries) and bound modules (functor arguments) return [None]. *)
Ltac2 @external parent_module : t -> t option
  := "rocq-runtime.plugins.ltac2" "module_parent_module".

(** Throws on [VarRef]. *)
Ltac2 @external module_of_reference : Std.reference -> t
  := "rocq-runtime.plugins.ltac2" "module_of_reference".

(** Returns a reference to the current innermost open interactive module. *)
Ltac2 @external current_module : unit -> t
  := "rocq-runtime.plugins.ltac2" "current_module".

Ltac2 @external loaded_libraries : unit -> t list
  := "rocq-runtime.plugins.ltac2" "module_loaded_libraries".

Module Field.
  (** This API is written using a record of functions to implement
      case analysis instead of exposing [t] as a sum type for forward compatibility:
      a case analysis can be written as [{ handle_nothing with ...}]
      and any new field kinds will be handled without error. *)

  (** Type of module fields. *)
  Ltac2 Type t.

  (** Information about rewrite rules. Currently nothing is exposed about it. *)
  Ltac2 Type rewrule.

  (** Case analysis over a module field. *)
  Ltac2 Type 'a handler := {
      handle_submodule : Module.t -> 'a;
      handle_reference : Std.reference -> 'a;
      handle_rewrule : rewrule -> 'a;
    }.

  (** Default case analysis. *)
  Ltac2 handle_nothing := {
      handle_submodule := (fun _ => None);
      handle_reference := (fun _ => None);
      handle_rewrule := (fun _ => None);
    }.

  (** Execute a case analysis. *)
  Ltac2 @external handle : t -> 'a handler -> 'a
    := "rocq-runtime.plugins.ltac2" "module_field_handle".

  (** Test whether a module field is a submodule (or sub-module type or sub-functor). *)
  Ltac2 is_submodule (f:t) : Module.t option :=
    handle f { handle_nothing with handle_submodule := (fun x => Some x) }.

  (** Test whether a module field is a reference. *)
  Ltac2 is_reference (f:t) : Std.reference option :=
    handle f { handle_nothing with handle_reference := (fun x => Some x) }.

End Field.

(** Return the contents of the given module. [None] on closed functors and module types.
    Inductives are represented only by the first inductive of each mutual block (and no constructors). *)
Ltac2 @external module_contents : t -> Field.t list option
  := "rocq-runtime.plugins.ltac2" "module_contents".

(** Deeply fold over references in the given module
    (e.g. if [mod] is [M] and contains submodule [M.N]
    which contains reference [M.N.x], [M.N.x] will be passed to [f]). *)
Ltac2 rec deep_fold_child_references (f:'a -> Std.reference -> 'a) (acc:'a) (mod:t) : 'a :=
  match module_contents mod with
  | None => acc
  | Some contents =>
      List.fold_left
        (fun acc field =>
           Field.handle field {
               Field.handle_submodule := (fun mod => deep_fold_child_references f acc mod);
               Field.handle_reference := (fun r => f acc r);
               Field.handle_rewrule := (fun _ => acc);
             })
        acc contents
  end.
