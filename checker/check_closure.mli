(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The statement report of [rocqchk -statement-report FILE]. *)

type request = {
  req_name : string;  (** a label, printed back as given *)
  req_model : string;  (** the constant whose closure is reported *)
  req_trusted : string option;  (** the constant whose type it must have *)
}

val read_requests : string -> request list
(** One request per line, [<name> <model> [<trusted>|-]], the tokens
    separated by single spaces; a constant is named by the string
    [Names.Constant.to_string] prints. Blank lines and lines starting with [#]
    are skipped. A tab or carriage return on any line is an error.
    @raise CErrors.UserError on any other line. *)

val print : Environ.env -> (Opaqueproof.opaque -> Opaqueproof.opaque_proofterm) ->
  request list -> unit
(** Print the report, one line per message on the feedback channel:

    {v
STATEMENT REPORT
statement <name> <model> <trusted|-> <verdict> <axiom-count> <flag-count>
axiom <name> <constant>
flag <name> <kind> <object>
END STATEMENT REPORT
    v}

    The verdict is [match] when [Definition f := model] ([Polymorphic] when
    the trusted constant is) is accepted for the field [Parameter f : T] of a
    sealing module type, T being the trusted constant's type and universes:
    the model's type is cumulative to T, a needed universe constraint being
    added when it is consistent with the environment (a polymorphic model at
    a monomorphic T is taken at fresh universes; a polymorphic T requires the
    model's universe context to be T's, and adds no constraint). It is
    [universes-differ] when the types need universe constraints the
    environment or T's context refuses, when the universe contexts differ,
    and for every polymorphic model whose universe context has sort variables
    or constraints: elaborating the definition can minimize those, and the
    check does not replay it, so the sealing may still accept such a model.
    It is [mismatch] when the types are not convertible, and otherwise
    [model-missing], [trusted-missing], or
    [not-requested] (no trusted constant).

    The verdict is about the two constants as the kernel stores them.
    Implicit arguments are elaboration data that the kernel never sees, so a
    model declared with maximal implicit arguments reads [match] when its
    type is the statement's. Whether a bare alias [Definition f := model]
    then elaborates depends on the context it is written in, which this
    checker does not see.

    The axioms are the constants
    without a body that the selected proof witness of the model constant's
    body and type reaches. A public term uses a body-bearing declaration in
    the final environment; a bodyless public declaration uses its module
    implementation, and its dependencies continue in that implementation
    view. This keeps an implementation proof's typing conditions from being
    replaced by an independent signature proof. Literal and array terms
    also reach their registered primitive type. The flags are the relaxed
    typing conditions of what they reach:
    [type-in-type], [unsafe-fixpoint], [unchecked-eliminations],
    [assumed-positive], [uip] and [indices-not-mattering]. Statements keep
    request order; axioms and flags are sorted. *)
