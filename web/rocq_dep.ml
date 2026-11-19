(* rocq dep, for wasm_of_ocaml. It is a separate program, as with the
   native rocq command: the toplevel and coqdeplib can't be linked together
   (they declare the same warnings). It always terminates with exit, so
   that the host knows the exit code (globalThis.jsoo_exit in a browser). *)
let () =
  Coqdeplib.Rocqdep_main.main (List.tl (Array.to_list Sys.argv));
  exit 0
