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
    are skipped.
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

    The verdict is [match] or [mismatch] (the model constant's type is or is
    not convertible to the trusted constant's), [universes-differ] (their
    universe contexts differ), [model-missing], [trusted-missing], or
    [not-requested] (no trusted constant). The axioms are the constants
    without a body that the model constant's body and type reach, through
    the implementations of module signatures too, and the flags are the relaxed
    typing conditions of what they reach: [type-in-type], [unsafe-fixpoint],
    [unchecked-eliminations], [assumed-positive], [uip] and
    [indices-not-mattering]. Statements keep the request order; axioms and
    flags are sorted. *)
