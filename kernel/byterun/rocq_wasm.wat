;; Implementation of the primitives of the Rocq kernel for wasm_of_ocaml.
;;
;; The bytecode VM (vm_compute) and the native compiler (native_compute) are
;; not available: Rocq must be run with "-bytecode-compiler no".
;; The primitives below are the ones called at initialization time; the
;; other VM primitives are left undefined, wasm_of_ocaml turns them into
;; functions raising an exception.
;;
;; Floating point arithmetic is implemented in OCaml (see the web profile
;; in kernel/dune), only next_up and next_down need a primitive.

(module
   (import "env" "caml_nextafter_float"
      (func $caml_nextafter_float (param f64) (param f64) (result f64)))

   (type $float (struct (field f64)))

   ;; ---------------------------------------------------------------------
   ;; VM (rocq_memory.c, rocq_fix_code.c, rocq_values.c)

   (func (export "init_rocq_vm") (param (ref eq)) (result (ref eq))
      (ref.i31 (i32.const 0)))

   ;; The values returned by these functions are only used by the VM
   (func (export "rocq_accumulate") (param (ref eq)) (result (ref eq))
      (ref.i31 (i32.const 0)))
   (func (export "rocq_makeaccu") (param (ref eq)) (result (ref eq))
      (ref.i31 (i32.const 0)))
   (func (export "rocq_pushpop") (param (ref eq)) (result (ref eq))
      (ref.i31 (i32.const 0)))

   ;; Only used by native_compute
   (func (export "rocq_curry2_1_addr") (param (ref eq)) (result (ref eq))
      (ref.i31 (i32.const 0)))

   ;; ---------------------------------------------------------------------
   ;; Float64 (rocq_float64.c)

   (func (export "rocq_next_up_byte") (param $x (ref eq)) (result (ref eq))
      (struct.new $float
         (call $caml_nextafter_float
            (struct.get $float 0 (ref.cast (ref $float) (local.get $x)))
            (f64.const inf))))

   (func (export "rocq_next_down_byte") (param $x (ref eq)) (result (ref eq))
      (struct.new $float
         (call $caml_nextafter_float
            (struct.get $float 0 (ref.cast (ref $float) (local.get $x)))
            (f64.const -inf))))
)
