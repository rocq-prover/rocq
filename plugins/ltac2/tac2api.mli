(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Tac2val
open Names

module CInt = Int

(** Interface for registering custom [FMap]/[FSet]. *)

module type MapType = sig
  (** to have less boilerplate we use S.elt rather than declaring a toplevel type t *)
  module S : CSig.USetS
  module M : CMap.UExtS with type key = S.elt and module Set := S
  type valmap
  val valmap_eq : (valmap, Tac2val.valexpr M.t) Util.eq
  val repr : S.elt Tac2ffi.repr
end

type ('a,'set,'map) map_tag

val map_tag_eq : ('a,'set1,'map1) map_tag -> ('b,'set2,'map2) map_tag ->
  ('a * 'set1 * 'map1, 'b * 'set2 * 'map2) Util.eq option

type any_map_tag = Any : _ map_tag -> any_map_tag
type tagged_set = TaggedSet : (_,'set,_) map_tag * 'set -> tagged_set
type tagged_map = TaggedMap : (_,_,'map) map_tag * 'map -> tagged_map

val map_tag_repr : any_map_tag Tac2ffi.repr
val set_repr : tagged_set Tac2ffi.repr
val map_repr : tagged_map Tac2ffi.repr

val tag_set : (_,'set,_) map_tag -> 'set -> Tac2val.valexpr
val tag_map : (_,_,'map) map_tag -> 'map -> Tac2val.valexpr

val register_map : ?plugin:string -> tag_name:string
  -> (module MapType with type S.elt = 'a and type S.t = 'set and type valmap = 'map)
  -> ('a,'set,'map) map_tag
(** Register a type on which we can use finite sets and maps.
    [tag_name] is the name used for the external to make the
    [Ltac2.FSet.Tags.tag] available. *)

val get_map : ('a,'set,'map) map_tag ->
  (module MapType with type S.elt = 'a and type S.t = 'set and type valmap = 'map)


(** Top-level module for Ltac2 OCaml APIs.

    Note: avoid [open Ltac2], as built-in Ltac2 types will shadow built-in OCaml types. *)
module Ltac2 : sig
  (** Built-in types *)
  type int = Int.t
  type string = String.t
  type char = Char.t
  type ident = Id.t
  type uint63 = Uint63.t
  type float = Float64.t
  type pstring = Pstring.t
  type meta = Constr.metavariable
  type evar = Evar.t
  type sort = Sorts.t
  type cast = Constr.cast_kind
  type instance = EConstr.EInstance.t
  type constant = Constant.t
  type inductive = Ind.t
  type constructor = Construct.t
  type projection = Projection.t
  type pattern = Pattern.constr_pattern
  type constr = EConstr.t
  type preterm = Ltac_pretype.closed_glob_constr
  type binder = Name.t EConstr.binder_annot * EConstr.types
  type message = Pp.t
  type ('a, 'b, 'c, 'd) format = Tac2types.format list
  type nonrec 'a array = 'a array
  type err = Exninfo.iexn
  type exn = Exninfo.iexn
  type exninfo = Exninfo.info

  module Array : sig
    val empty : valexpr

    val make : int -> valexpr -> valexpr Proofview.tactic

    val length : int * valexpr array -> int
    val get : int * valexpr array -> int -> valexpr Proofview.tactic
    val set : int * valexpr array -> int -> valexpr -> unit Proofview.tactic

    val lowlevel_blit :
      int * valexpr array ->
      int ->
      int * valexpr array ->
      int ->
      int ->
      unit Proofview.tactic

    val lowlevel_fill :
      int * valexpr array -> int -> int -> valexpr -> unit Proofview.tactic

    val concat :
      (int * valexpr array) list -> valexpr
  end

  module Char : sig
    type t = char

    val of_int : int -> t Proofview.tactic
    val to_int : t -> int
  end

  module Constant : sig
    type t = constant

    val equal : t -> t -> bool
    val print : t -> message
  end

  module Constr : sig
    type t = constr

    val type_ : t -> valexpr Proofview.tactic
    val equal : t -> t -> bool Proofview.tactic

    module Binder : sig
      type t = binder
      type relevance = Sorts.relevance

      val make :
        ident option ->
        constr ->
        t Proofview.tactic

      val unsafe_make :
        ident option ->
        relevance ->
        constr ->
        t

      val name : t -> ident option
      val type_ : t -> constr
      val relevance : t -> relevance
    end

    module Relevance : sig
      type t = Binder.relevance

      val equal : t -> t -> Environ.env -> Evd.evar_map -> bool

      val relevant : t
      val irrelevant : t
    end

    module Unsafe : sig
      val kind : t -> Environ.env -> Evd.evar_map -> valexpr

      val make : valexpr -> Environ.env -> Evd.evar_map -> t

      val check : t -> valexpr Proofview.tactic

      val liftn : int -> int -> t -> t

      val substnl : EConstr.Vars.substl -> int -> t -> t

      val closenl : ident list -> int -> t -> t Proofview.tactic

      val closednl : int -> t -> bool Proofview.tactic

      val noccur_between :
        int -> int -> t -> bool Proofview.tactic

      val case :
        inductive -> valexpr Proofview.tactic

      type case = Constr.case_info

      module Case : sig
        val equal : case -> case -> bool
        val inductive : case -> inductive
      end
    end

    module Cast : sig
      type t = cast

      val default : valexpr
      val vm : valexpr
      val native : valexpr

      val equal : t -> t -> bool
    end

    val in_context :
      variable ->
      t ->
      (unit -> unit Proofview.tactic) ->
      t Proofview.tactic

    module Pretype : sig
      type expected_type = Pretyping.typing_constraint

      module Flags : sig
        type t = Pretyping.inference_flags

        val constr_flags : t

        val set_use_coercion : bool -> t -> t
        val set_use_typeclasses : bool -> t -> t
        val set_allow_evars : bool -> t -> t
        val set_nf_evars : bool -> t -> t
      end

      val expected_istype : expected_type

      val expected_oftype :
        constr -> expected_type

      val expected_without_type_constraint :
        expected_type

      val pretype :
        Flags.t ->
        expected_type ->
        preterm ->
        constr Proofview.tactic
    end

    val has_evar : t -> bool Proofview.tactic
  end

  module Constructor : sig
    type t = constructor

    val equal : t -> t -> bool

    val inductive : t -> inductive
    val index : t -> int
    val print : t -> message
  end

  module Control : sig
    val throw : exn -> 'a Proofview.tactic

    val zero : exn -> 'a Proofview.tactic

    val plus :
      (unit -> 'a Proofview.tactic) ->
      (exn -> 'a Proofview.tactic) ->
      'a Proofview.tactic

    val once :
      (unit -> 'a Proofview.tactic) -> 'a Proofview.tactic

    val case :
      (unit -> 'a Proofview.tactic) ->
      ('a * (exn -> 'a Proofview.tactic), exn) result Proofview.tactic

    val numgoals : unit -> int Proofview.tactic

    val dispatch :
      (unit -> unit Proofview.tactic) list ->
      unit Proofview.tactic

    val extend :
      (unit -> unit Proofview.tactic) list ->
      (unit -> unit Proofview.tactic) ->
      (unit -> unit Proofview.tactic) list ->
      unit Proofview.tactic

    val enter :
      (unit -> 'a Proofview.tactic) -> unit Proofview.tactic

    val focus :
      int ->
      int ->
      (unit -> 'a Proofview.tactic) ->
      'a Proofview.tactic

    val shelve : unit -> unit Proofview.tactic
    val shelve_unifiable : unit -> unit Proofview.tactic

    val unshelve :
      (unit -> 'a Proofview.tactic) -> 'a Proofview.tactic

    val new_goal : Proofview_monad.goal -> unit Proofview.tactic
    val cycle : int -> unit Proofview.tactic
    val reorder_goals : Int.t list -> unit Proofview.tactic
    val goal : unit -> constr Proofview.tactic
    val hyp : variable -> constr Proofview.tactic

    val hyp_value :
      variable -> constr option Proofview.tactic

    val hyps : unit -> valexpr Proofview.tactic

    val refine :
      (unit -> constr Proofview.tactic) ->
      unit Proofview.tactic

    val solve_constraints : unit -> unit Proofview.tactic

    val with_holes :
      (unit -> 'a Proofview.tactic) ->
      ('a -> 'b Proofview.tactic) ->
      'b Proofview.tactic

    val progress :
      (unit -> 'a Proofview.tactic) -> 'a Proofview.tactic

    val abstract :
      ident option ->
      (unit -> unit Proofview.tactic) ->
      unit Proofview.tactic

    val time :
      string option ->
      (unit -> 'a Proofview.tactic) ->
      'a Proofview.tactic

    val timeout :
      int -> (unit -> 'a Proofview.tactic) -> 'a Proofview.tactic

    val timeoutf :
      float ->
      (unit -> 'a Proofview.tactic) ->
      'a Proofview.tactic

    val check_interrupt : unit -> unit Proofview.tactic
    val clear_err_info : err -> err
    val current_exninfo : unit -> exninfo Proofview.tactic
    val print_err : err -> message

    val throw_bt : exn -> exninfo -> 'b Proofview.tactic

    val zero_bt : exn -> exninfo -> 'a Proofview.tactic

    val plus_bt :
      (unit -> 'a Proofview.tactic) ->
      (exn -> exninfo -> 'a Proofview.tactic) ->
      'a Proofview.tactic
  end

  module Env : sig
    val get : ident list -> GlobRef.t option
    val expand : ident list -> GlobRef.t list

    val path : GlobRef.t -> ident list Proofview.tactic

    val instantiate : GlobRef.t -> constr Proofview.tactic
  end

  module Evar : sig
    type t = evar

    val equal : t -> t -> bool
  end

  module Float : sig
    type t = float

    val equal : t -> t -> bool
  end

  module Fresh : sig
    module Free : sig
      type t = Nameops.Fresh.t

      val empty : t
      val add : ident -> t -> t

      val union : t -> t -> t

      val of_ids : ident list -> t
      val of_constr : constr -> t Proofview.tactic
    end

    val next : Free.t -> ident -> ident * Free.t
    val fresh : Free.t -> ident -> ident
  end

  module Ident : sig
    type t = ident

    val equal : ident -> ident -> bool
    val to_string : ident -> string
    val of_string : string -> ident option
  end

  module Ind : sig
    type t = inductive
    type data = inductive * Declarations.mutual_inductive_body

    val equal : t -> t -> bool

    val data : t -> data Proofview.tactic

    val repr : data -> t
    val index : t -> int
    val nblocks : data -> int

    val nconstructors : data -> int

    val get_block : data -> int -> data Proofview.tactic

    val get_constructor : data -> int -> constructor Proofview.tactic

    val nparams : data -> int
    val nparams_uniform : data -> int

    val get_projections : data -> projection array option

    val constructor_nargs : data -> int array
    val constructor_ndecls : data -> int array

    val print : t -> message
  end

  module Int : sig
    type t = int

    val equal : 'a -> 'a -> bool
    val compare : int -> int -> int
    val add : int -> int -> int
    val sub : int -> int -> int
    val mul : int -> int -> int
    val div : int -> int -> int Proofview.tactic
    val ( mod ) : int -> int -> int Proofview.tactic
    val neg : int -> int
    val abs : int -> int
    val ( asr ) : int -> int -> int
    val ( lsl ) : int -> int -> int
    val ( lsr ) : int -> int -> int
    val ( land ) : int -> int -> int
    val ( lor ) : int -> int -> int
    val ( lxor ) : int -> int -> int
    val lnot : int -> int
  end

  module Message : sig
    val print : message -> unit
    val empty : message
    val of_string : string -> message
    val to_string : message -> string
    val of_int : int -> message
    val of_ident : ident -> message
    val of_constr : constr -> message Proofview.tactic
    val of_lconstr : constr -> message Proofview.tactic

    val of_preterm : preterm -> message Proofview.tactic
    val of_lpreterm : preterm -> message Proofview.tactic

    val of_exn : valexpr -> Environ.env -> Evd.evar_map -> message
    val of_exninfo : exninfo -> message

    val concat : message -> message -> message
    val force_new_line : message
    val break : int -> int -> message
    val space : message
    val hbox : message -> message
    val vbox : int -> message -> message
    val hvbox : int -> message -> message
    val hovbox : int -> message -> message

    module Format : sig
      val stop : ('a, 'b, 'c, 'a) format
      val string : ('a, 'b, 'c, 'd) format -> (string -> 'a, 'b, 'c, 'd) format
      val int : ('a, 'b, 'c, 'd) format -> (int -> 'a, 'b, 'c, 'd) format
      val constr : ('a, 'b, 'c, 'd) format -> (constr -> 'a, 'b, 'c, 'd) format
      val ident : ('a, 'b, 'c, 'd) format -> (ident -> 'a, 'b, 'c, 'd) format

      val message : ('a, 'b, 'c, 'd) format -> (message -> 'a, 'b, 'c, 'd) format

      val literal : string -> ('a, 'b, 'c, 'd) format -> ('a, 'b, 'c, 'd) format

      val alpha : ('a, 'b, 'c, 'd) format -> (('b -> 'r -> 'c) -> 'r -> 'a, 'b, 'c, 'd) format
      val alpha0 : ('a, 'b, 'c, 'd) format -> (('r -> 'c) -> 'r -> 'a, 'b, 'c, 'd) format

      val kfprintf :
        Tac2val.closure ->
        ('a, unit, message, 'r) format ->
        valexpr Proofview.tactic

      val ikfprintf :
        Tac2val.closure ->
        valexpr ->
        ('a, unit, 'v, 'r) format ->
        valexpr Proofview.tactic
    end
  end

  module Meta : sig
    type t = meta

    val equal : t -> t -> bool
  end

  module Module : sig
    type t = ModPath.t

    val equal : t -> t -> bool
    val to_message : t -> message

    val is_modtype : t -> Environ.env -> Evd.evar_map -> bool
    val is_functor : t -> Environ.env -> Evd.evar_map -> bool
    val is_bound_module : t -> bool
    val is_library : t -> bool
    val is_open : t -> bool

    val parent_module : t -> t option

    val module_of_reference : GlobRef.t -> t Proofview.tactic

    val current_module : unit -> t
    val loaded_libraries : unit -> t list

    module Field : sig
      type t = Tac2ffi.ModField.t

      val handle :
        t ->
        (ModPath.t -> 'a)
        * (GlobRef.t -> 'a)
        * (unit -> 'a) ->
        'a
    end

    val contents : t -> Field.t list option
  end

  module Pattern : sig
    type context = Constr_matching.context

    val empty_context : context

    val matches : pattern -> constr -> valexpr Proofview.tactic

    val matches_subterm : pattern -> constr -> (context * (ident * constr) list) Proofview.tactic

    val matches_vect : pattern -> constr -> valexpr Proofview.tactic

    val matches_subterm_vect : pattern -> constr -> (context * constr array) Proofview.tactic

    val matches_goal :
      bool ->
      Tac2match.match_context_hyps list ->
      Tac2match.match_pattern ->
      valexpr Proofview.tactic

    val instantiate : context -> constr -> constr
  end

  module Proj : sig
    type t = projection

    val equal : t -> t -> bool

    val ind : t -> inductive
    val index : t -> int

    val unfolded : t -> bool
    val set_unfolded : t -> bool -> t

    val of_constant : constant -> t option
    val to_constant : t -> constant option

    val print : t -> message
  end

  module Pstring : sig
    type t = pstring
    type char63 = uint63

    val max_length : uint63
    val to_string : t -> string
    val of_string : string -> t option
    val make : uint63 -> char63 -> t
    val length : t -> uint63
    val get : t -> uint63 -> char63
    val sub : t -> uint63 -> uint63 -> t
    val cat : t -> t -> t
    val equal : t -> t -> bool
    val compare : t -> t -> int
  end

  module Rewrite : sig
    module Strategy : sig
      type t = Rewrite.strategy

      val id : t
      val fail : t
      val refl : t
      val progress : t -> t

      val seq : t -> t -> t
      val seqs : t list -> t

      val choice : t -> t -> t
      val choices : t list -> t

      val try_ : t -> t

      val fix_ : Tac2val.closure -> t Proofview.tactic

      val any : t -> t
      val repeat : t -> t
      val one_subterm : t -> t
      val all_subterms : t -> t
      val bottomup : t -> t
      val topdown : t -> t
      val innermost : t -> t
      val outermost : t -> t
      val hints : ident -> t
      val old_hints : ident -> t

      val one_lemma : preterm -> bool -> t

      val lemmas : preterm list -> t

      val fold : constr -> t
      val eval : Redexpr.red_expr -> t
      val matches : pattern -> t

      val tactic :
        (constr ->
         constr ->
         constr option ->
         Rewrite.rewrite_result Proofview.tactic) ->
        t
    end

    val rewrite_strat :
      Strategy.t ->
      ident option ->
      unit Proofview.tactic
  end

  module Scheme : sig
    type kind = string

    val lookup : kind -> GlobRef.t -> GlobRef.t option

    val rect_dep : kind
    val rec_dep : kind
    val ind_dep : kind
    val sind_dep : kind
    val ind_nodep : kind
    val rec_nodep : kind
    val rect_nodep : kind
    val sind_nodep : kind
    val eq_dec : kind
    val dec_lb : kind
    val dec_bl : kind
    val beq : kind
    val congr : kind
    val rew_fwd_r_dep : kind
    val rew_r_dep : kind
    val rew_r : kind
    val rew_fwd_dep : kind
    val rew_dep : kind
    val rew : kind
    val sym_involutive : kind
    val sym : kind
    val scase_nodep : kind
    val scase_dep : kind
    val casep_nodep : kind
    val casep_dep : kind
    val case_nodep : kind
    val case_dep : kind
  end

  module Std = Tac2stdlib.Ltac2Std

  module String : sig
    type t = bytes

    val make : int -> char -> t Proofview.tactic
    val length : t -> int
    val set : t -> int -> char -> unit Proofview.tactic
    val get : t -> int -> char Proofview.tactic
    val concat : t -> t list -> t
    val app : t -> t -> t
    val sub : t -> int -> int -> t Proofview.tactic

    val equal : t -> t -> bool
    val compare : t -> t -> int
  end

  module Uint63 : sig
    type t = uint63

    val of_int : int -> t

    val equal : t -> t -> bool
    val compare : t -> t -> int

    val print : t -> message
  end

  module FSet : sig
    module Tags : sig
      val ident_tag :
        ( ident,
          Id.Set.t,
          valexpr Id.Map.t )
          map_tag

      val int_tag :
        (int, CInt.Set.t, valexpr CInt.Map.t) map_tag

      val inductive_tag :
        ( inductive,
          Indset_env.t,
          valexpr Indmap_env.t )
          map_tag

      val constructor_tag :
        ( constructor,
          Constrset_env.t,
          valexpr Constrmap_env.t )
          map_tag

      val constant_tag :
        ( constant,
          Cset_env.t,
          valexpr Cmap_env.t )
          map_tag

      val string_tag :
        ( CString.t,
          CString.Set.t,
          valexpr CString.Map.t )
          map_tag
    end

    val empty : any_map_tag -> valexpr
    val is_empty : tagged_set -> bool
    val mem : valexpr -> tagged_set -> bool
    val add : valexpr -> tagged_set -> valexpr
    val remove : valexpr -> tagged_set -> valexpr
    val union : tagged_set -> tagged_set -> valexpr
    val inter : tagged_set -> tagged_set -> valexpr
    val diff : tagged_set -> tagged_set -> valexpr
    val equal : tagged_set -> tagged_set -> bool
    val subset : tagged_set -> tagged_set -> bool
    val cardinal : tagged_set -> int
    val elements : tagged_set -> valexpr
  end

  module FMap : sig
    val empty : any_map_tag -> valexpr
    val is_empty : tagged_map -> bool
    val mem : valexpr -> tagged_map -> bool

    val add :
      valexpr ->
      valexpr ->
      tagged_map ->
      valexpr

    val remove : valexpr -> tagged_map -> valexpr

    val find_opt :
      valexpr -> tagged_map -> valexpr option

    val mapi :
      Tac2val.closure ->
      tagged_map ->
      valexpr Proofview.tactic

    val fold :
      Tac2val.closure ->
      tagged_map ->
      valexpr ->
      valexpr Proofview.Monad.t

    val cardinal : tagged_map -> int
    val bindings : tagged_map -> valexpr
    val domain : tagged_map -> valexpr
  end

  module TransparentState : sig
    type t = TransparentState.t
    type strategy_level = Conv_oracle.level

    val empty : t
    val full : t
    val current : unit -> t Proofview.tactic

    val union : t -> t -> t
    val inter : t -> t -> t
    val diff : t -> t -> t

    val add_constant : constant -> t -> t
    val add_proj : projection -> t -> t
    val add_var : ident -> t -> t

    val remove_constant : constant -> t -> t
    val remove_proj : projection -> t -> t
    val remove_var : ident -> t -> t

    val mem_constant : constant -> t -> bool
    val mem_proj : projection -> t -> bool
    val mem_var : ident -> t -> bool

    val with_strategy :
      strategy_level ->
      GlobRef.t list ->
      (unit -> 'a Proofview.tactic) ->
      'a Proofview.tactic
  end

  module Unification : sig
    type conv_flag = Evd.conv_pb

    val conv :
      conv_flag ->
      TransparentState.t ->
      constr ->
      constr ->
      bool Proofview.tactic

    val unify :
      TransparentState.t ->
      constr ->
      constr ->
      unit Proofview.tactic
  end
end
