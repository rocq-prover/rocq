(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s This module declares the extraction commands. *)

open Names
open Libnames

(* these functions modify the summary because they call
   output_directory which sets the directory if it was not already
   set. *)

val simple_extraction : Summary.Interp.mut -> opaque_access:Global.indirect_accessor -> qualid -> unit
val full_extraction : Summary.Interp.mut -> opaque_access:Global.indirect_accessor -> string option -> qualid list -> unit
val separate_extraction : Summary.Interp.mut -> opaque_access:Global.indirect_accessor -> qualid list -> unit
val extraction_library : Summary.Interp.mut -> opaque_access:Global.indirect_accessor -> bool -> lident -> unit

(* For the test-suite : extraction to a temporary file + ocamlc on it *)

val extract_and_compile : Summary.Interp.mut -> opaque_access:Global.indirect_accessor -> qualid list -> unit

(* For debug / external output via coqtop.byte + Drop : *)

val mono_environment :
 Common.State.t -> opaque_access:Global.indirect_accessor -> Miniml.global list -> ModPath.t list -> Miniml.ml_structure

(* Used by the Relation Extraction plugin *)

val print_one_decl :
  Common.State.t -> Miniml.ml_structure -> ModPath.t -> Miniml.ml_decl -> Pp.t

(* Show the extraction of the current ongoing proof *)

val show_extraction : pstate:Declare.Proof.t -> unit
