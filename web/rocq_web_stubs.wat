;; Primitives used by the Rocq libraries that the wasm_of_ocaml runtime does
;; not provide
(module
   (import "env" "caml_failwith" (func $caml_failwith (param (ref eq))))

   (type $bytes (array (mut i8)))

   ;; ---------------------------------------------------------------------
   ;; Threads: there is only one thread, Thread.create fails
   (@string $no_threads "Thread.create: threads are not available")

   (func (export "caml_thread_initialize") (param (ref eq)) (result (ref eq))
      (ref.i31 (i32.const 0)))
   (func (export "caml_thread_cleanup") (param (ref eq)) (result (ref eq))
      (ref.i31 (i32.const 0)))
   (func (export "caml_thread_yield") (param (ref eq)) (result (ref eq))
      (ref.i31 (i32.const 0)))
   (func (export "caml_thread_join") (param (ref eq)) (result (ref eq))
      (ref.i31 (i32.const 0)))
   (func (export "caml_thread_uncaught_exception") (param (ref eq)) (result (ref eq))
      (ref.i31 (i32.const 0)))
   (func (export "caml_thread_self") (param (ref eq)) (result (ref eq))
      (ref.i31 (i32.const 0)))
   (func (export "caml_thread_id") (param (ref eq)) (result (ref eq))
      (ref.i31 (i32.const 0)))
   (func (export "caml_thread_new") (param (ref eq)) (result (ref eq))
      (call $caml_failwith (global.get $no_threads))
      (ref.i31 (i32.const 0)))

   ;; ---------------------------------------------------------------------
   ;; Unix
   (func (export "caml_unix_getpid") (param (ref eq)) (result (ref eq))
      (ref.i31 (i32.const 1)))
)
