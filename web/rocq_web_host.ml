(* What the JavaScript host of a Rocq program compiled with wasm_of_ocaml
   needs from the program. When the program starts (init), it calls the
   function globalThis.rocqWebInit, if the host defined it, with an object
   with two functions:

   - mount(path) mounts an in-memory device at path, in the pseudo
     filesystem of the runtime. Under node, the files of the computer are
     the ones of the real file system, and the host can create files with
     globalThis.jsoo_create_file only in an in-memory device: e.g. to
     create the files of a published opam switch, fetched when they are
     read, at the prefix of the switch. A path in the device which the
     host did not create does not exist.

   - readFile(name) returns the content of a file as a Uint8Array, or null
     if there is no such file: e.g. to get the files written by the
     program once it exited, outside of node. *)

open Js_of_ocaml

let mount path =
  Sys_js.mount ~path:(Js.to_string path) (fun ~prefix:_ ~path:_ -> None)

let read_file name =
  match Sys_js.read_file ~name:(Js.to_string name) with
  | s -> Js.some (Typed_array.Bytes.to_uint8Array (Bytes.of_string s))
  | exception Sys_error _ -> Js.null

let init () =
  let f = Js.Unsafe.get Js.Unsafe.global "rocqWebInit" in
  if Js.Optdef.test f then
    ignore (Js.Unsafe.fun_call f [| Js.Unsafe.obj [|
      "mount", Js.Unsafe.inject (Js.wrap_callback mount);
      "readFile", Js.Unsafe.inject (Js.wrap_callback read_file);
    |] |])
