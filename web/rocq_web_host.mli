(** What the JavaScript host of a Rocq program compiled with wasm_of_ocaml
    needs from the program (see rocq_web_host.ml). *)

val init : unit -> unit
(** Call globalThis.rocqWebInit, if defined, with the functions mount and
    readFile. To be called when the program starts. *)
