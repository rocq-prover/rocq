(* rocq c (rocq compile), for wasm_of_ocaml. It always terminates with
   exit, so that the host knows the exit code (globalThis.jsoo_exit in a
   browser). *)
let () =
  (* Plugins are bytecode, loaded with Dynlink, which by default refuses
     units declaring external primitives (e.g. atdgen-runtime, needed by
     rocq-elpi). Native Dynlink does not check this, so Rocq never asks:
     allow them; a missing primitive is reported when linking the plugin. *)
  Dynlink.allow_unsafe_modules true;
  Coqc.main (List.tl (Array.to_list Sys.argv))
