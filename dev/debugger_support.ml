(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let rawdebug = ref false

let cur_summary = ref @@ Summary.init()

let () =
  Flags.in_debugger := true;
  Summary.run_synterp_interp
    (fun sum -> ())
    (fun sum () ->
       Goptions.set_bool_option_value InterpG sum ["Printing";"Existential";"Instances"] true;
       PrintingFlags.print_universes := true;
       Goptions.set_bool_option_value InterpG sum ["Printing";"Matching"] false;
       Goptions.set_bool_option_value InterpG sum ["Printing";"Sort";"Qualities"] true)
    cur_summary;
  (* When printers are used from ocamldebug, they should not make calls to the global env
     since ocamldebug runs in a different process and does not have the proper env at hand *)
  Constrextern.set_extern_reference (if !rawdebug then Top_printers.raw_string_of_ref else Top_printers.short_string_of_ref)
