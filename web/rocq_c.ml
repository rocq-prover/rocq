(* rocq c (rocq compile), for wasm_of_ocaml. It always terminates with
   exit, so that the host knows the exit code (globalThis.jsoo_exit in a
   browser). *)
let () = Coqc.main (List.tl (Array.to_list Sys.argv))
