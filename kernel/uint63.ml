(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* The implementation is chosen at run time, depending on the size of OCaml
   integers:
   - 63 bits: Uint63_63, where an uint63 is an immediate integer;
   - otherwise (32 bits machines, js_of_ocaml, wasm_of_ocaml): Uint63_web,
     where an uint63 is a boxed Int64, which also accepts the immediates
     found in the .vo files produced by a 64 bits Rocq.

   This way the bytecode of the Rocq libraries runs on both. For instance
   wasm_of_ocaml can link the libraries of a native Rocq, and load its
   plugins. In native code [Sys.int_size] is a constant, hence the choice
   is made at compile time: the conditional and the unpacking of the
   module are simplified away, and the functions are still inlined. *)

include (val (if Sys.int_size >= 63
               then (module Uint63_63 : Uint63_intf.S)
               else (module Uint63_web : Uint63_intf.S)) : Uint63_intf.S)
