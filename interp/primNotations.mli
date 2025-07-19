(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Glob_term
open Names

type rawnum = NumTok.Signed.t

(** The unique id string below will be used to refer to a particular
    registered interpreter/uninterpreter of number or string notation.
    Using the same uid for different (un)interpreters will fail.
    If at most one interpretation of prim token is used per scope,
    then the scope name could be used as unique id. *)

type prim_token_uid = private string

type 'a prim_token_interpreter = ?loc:Loc.t -> 'a -> glob_constr
type 'a prim_token_uninterpreter = any_glob_constr -> 'a option

type 'a prim_token_interpretation =
  'a prim_token_interpreter * 'a prim_token_uninterpreter

val register_rawnumeral_interpretation :
  ?allow_overwrite:bool -> string -> rawnum prim_token_interpretation -> prim_token_uid

val register_bignumeral_interpretation :
  ?allow_overwrite:bool -> string -> Z.t prim_token_interpretation -> prim_token_uid

val register_string_interpretation :
  ?allow_overwrite:bool -> string -> string prim_token_interpretation -> prim_token_uid

(** * Number notation *)

type prim_token_notation_error =
  | UnexpectedTerm of Constr.t
  | UnexpectedNonOptionTerm of Constr.t

exception PrimTokenNotationError of string * Environ.env * Evd.evar_map * prim_token_notation_error

type numnot_option =
  | Nop
  | Warning of NumTok.UnsignedNat.t
  | Abstract of NumTok.UnsignedNat.t

type int_ty =
  { dec_uint : Names.inductive;
    dec_int : Names.inductive;
    hex_uint : Names.inductive;
    hex_int : Names.inductive;
    uint : Names.inductive;
    int : Names.inductive }

type z_pos_ty =
  { z_ty : Names.inductive;
    pos_ty : Names.inductive }

type number_ty =
  { int : int_ty;
    decimal : Names.inductive;
    hexadecimal : Names.inductive;
    number : Names.inductive }

type pos_neg_int63_ty =
  { pos_neg_int63_ty : Names.inductive }

type target_kind =
  | Int of int_ty (* Corelib.Init.Number.int + uint *)
  | UInt of int_ty (* Corelib.Init.Number.uint *)
  | Z of z_pos_ty (* Corelib.Numbers.BinNums.Z and positive *)
  | Int63 of pos_neg_int63_ty (* Corelib.Numbers.Cyclic.Int63.PrimInt63.pos_neg_int63 *)
  | Float64 (* Corelib.Floats.PrimFloat.float *)
  | Number of number_ty (* Corelib.Init.Number.number + uint + int *)

type string_target_kind =
  | ListByte
  | Byte
  | PString

type option_kind = Direct | Option | Error
type 'target conversion_kind = 'target * option_kind

(** A postprocessing translation [to_post] can be done after execution
   of the [to_ty] interpreter. The reverse translation is performed
   before the [of_ty] uninterpreter.

   [to_post] is an array of [n] lists [l_i] of tuples [(f, t,
   args)]. When the head symbol of the translated term matches one of
   the [f] in the list [l_0] it is replaced by [t] and its arguments
   are translated acording to [args] where [ToPostCopy] means that the
   argument is kept unchanged and [ToPostAs k] means that the
   argument is recursively translated according to [l_k].
   [ToPostHole] introduces an additional implicit argument hole
   (in the reverse translation, the corresponding argument is removed).
   [ToPostCheck r] behaves as [ToPostCopy] except in the reverse
   translation which fails if the copied term is not [r].
   When [n] is null, no translation is performed. *)
type to_post_arg = ToPostCopy | ToPostAs of int | ToPostHole of Id.t | ToPostCheck of Constr.t
type ('target, 'warning) prim_token_notation_obj =
  { to_kind : 'target conversion_kind;
    to_ty : GlobRef.t;
    to_post : ((GlobRef.t * GlobRef.t * to_post_arg list) list) array;
    of_kind : 'target conversion_kind;
    of_ty : GlobRef.t;
    ty_name : Libnames.qualid; (* for warnings / error messages *)
    warning : 'warning }

type number_notation_obj = (target_kind, numnot_option) prim_token_notation_obj
type string_notation_obj = (string_target_kind, unit) prim_token_notation_obj

type prim_token_interp_info =
  | Uid of prim_token_uid
  | NumberNotation of number_notation_obj
  | StringNotation of string_notation_obj

val do_interp : ?loc:Loc.t -> prim_token_interp_info -> Constrexpr.prim_token -> Glob_term.glob_constr

val do_uninterp : prim_token_interp_info -> _ Glob_term.glob_constr_g -> Constrexpr.prim_token option

val can_interp : prim_token_interp_info -> Constrexpr.prim_token -> bool

(** Conversion from bigint to int63 *)
val int63_of_pos_bigint : Z.t -> Uint63.t
