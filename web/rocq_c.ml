(* rocq c (rocq compile), for wasm_of_ocaml. It always terminates with
   exit, so that the host knows the exit code (globalThis.jsoo_exit in a
   browser). *)
let () =
  (* Plugins are bytecode, loaded with Dynlink, which by default refuses
     units declaring external primitives (e.g. atdgen-runtime, needed by
     rocq-elpi). Native Dynlink does not check this, so Rocq never asks:
     allow them; a missing primitive is reported when linking the plugin. *)
  Rocq_web_host.init ();
  Dynlink.allow_unsafe_modules true;
  (* The bytecode of the VM cannot be run (vm_compute falls back to cbv),
     and making it calls C primitives that wasm_of_ocaml does not have,
     e.g. for the number notations: by default, do not make it. Options
     are read in order: -bytecode-compiler yes on the command line wins. *)
  Coqc.main ("-bytecode-compiler" :: "no" :: List.tl (Array.to_list Sys.argv))
