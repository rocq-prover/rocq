open Names
(* kernel names, ie ModPath, KerName, Id etc *)

open Ltac2_plugin
(* the Ltac2 plugin is "packaged" ie its modules are all contained in module Ltac2_plugin
   without this open we would have to refer to eg Ltac2_plugin.Tac2externals below *)

open Tac2externals
(* APIs to register new externals, including the convenience "@->" infix operator *)

open Tac2ffi
(* Translation operators between Ltac2 values and OCaml values in various types *)

(** **** Two simple examples of tactics *)

(* Rocq tactics are values of the [Proofview.tactic] monad.
   tclUnit in Proofview is the return operation of this monad.
   We define an alias for convenience. *)
let return = Proofview.tclUNIT

(* Used to distinguish our primitives from some other plugin's primitives.
   By convention matches the plugin's ocamlfind name. *)
let plugin_name = "rocq-plugin-tutorial.tuto4"

let pname s = { Tac2expr.mltac_plugin = plugin_name; mltac_tactic = s }

(* We define for convenience a wrapper around Tac2externals.define.
   [define "foo"] has type
   [('a, 'b) Ltac2_plugin.Tac2externals.spec -> 'b -> unit].
   Type [('a, 'b) spec] represents a high-level Ltac2 tactic specification. It
   indicates how to turn a value of type ['b] into an Ltac2 tactic.
   The type parameter ['a] gives the type of value produced by interpreting the
   specification. *)
let define s = define (pname s)

(* We define a tactic taking an Ltac2 integer and returning an Ltac2 boolean
   "@->" is an infix function from Tac2externals combining a "type representation"
   (Tac2ffi.repr) and a [Tac2externals.spec].
   Here, [int @-> ret bool] means that we want to define an Ltac2 tactic which
   takes an Ltac2 int and returns an Ltac2 bool.
   [ret] means we return the answer without doing tactic operations
   (no access to the Proofview monad). *)
let () = define "the_question" (int @-> ret bool) @@ fun i ->
  Int.equal i 42

(* Now, we define a wrapper around "exact", it takes a constr
   (ie a term) and returns the trivial value (and does side effects on the goal).
   "tac" means we have access to the tactic monad. *)
let () = define "my_exact" (constr @-> tac unit) @@ fun c ->
  Tactics.exact_check c

(* We can see our new Ltac2 tactics in action in the beginning of the
   theories/Demo.v file. *)

(** **** Transparent custom type *)

(* We have seen before how to use the int and bool "reprs" (representations) in Ltac2.
   In this section, we will learn to define a "repr" for a custom OCaml type. *)

(* We define a custom type in OCaml and in Ltac2 (this is the OCaml side): *)
type my_custom =
  | A
  | B of EConstr.t
  (* EConstr.t is the type of terms (it wraps around the kernel
     Constr.t to enforce invariants when handling terms with
     existential variables). *)

(* Translate from OCaml to the Ltac2 representation (Tac2val.valexpr).

   Values of Ltac2 algebraic datatypes are represented

   - for constant (without arguments) constructors, by ValInt where
     the int is the 0-based index of the constructor (excluding
     non-constant constructors)

   - for non-constant (with arguments) constructors, by ValBlk where
     the first argument is the 0-based index of the constructor (excluding constant constructors)
     and the second is an array containing the arguments.

   eg with [Ltac2 Type foo := [ A | B (x) | C | D (y, z) ]],
   - [A] is [ValInt 0]
   - [B v] is [ValBlk (0, [|v|])]
   - [C] is [ValInt 1]
   - [D v1 v2] is [ValBlk (1, [|v1; v2|])]

   When building values from OCaml we can use [of_int] and [of_block]
   instead of [ValInt] and [ValBlk].
*)
let of_custom = function
  | A -> of_int 0
  | B c ->
    (* Here [of_constr] is [Tac2ffi.of_constr] *)
    of_block (0, [|of_constr c|])

(* Go from the Ltac2 representation to the OCaml representation.
   This needs to look at the low-level valexpr data.
   If an external is declared with an incorrect Ltac2 type it may be passed
   invalid values, in which case we assert false. *)
let to_custom = let open Tac2val in function
  | ValInt 0 -> A
  | ValBlk (0, [|c|]) ->
    (* [to_constr] is [Tac2ffi.to_constr] *)
    B (to_constr c)
  | _ -> assert false


(* Now we package both translation functions into a Tac2ffi.repr
   which is just a record holding these two translation functions *)
let custom = make_repr of_custom to_custom

(* We can now use custom just like we used the "int" and "bool" reprs before.
   For instance, here is a tactic returning true if passed [A] or [B] of some
   inductive type.
   We need the evar map to inspect the term in the B case,
   but we don't need the current goal's hypotheses, so we use "eret"
   (in fact we don't use the environment at all).
*)
let () = define "is_ind_or_a" (custom @-> eret bool) @@ fun v env sigma ->
  match v with
  | A -> true
  | B c -> EConstr.isInd sigma c

(* We can now use custom just like we used the "int" and "bool" reprs before.
   For instance, here is a tactic returning true if passed [A] or [B] of some
   inductive type.

   We need the evar map to inspect the term in the B case,
   but we don't need the current goal's hypotheses, so we use "eret"
   (in fact we don't use the environment at all).

   We could also use "gret", but that fails (with an anomaly) when 0 goals are focused.
*)
let () = define "check_in_goal" (ident @-> tac custom) @@ fun id ->
  (* pf_apply gives us the "current" environment, ie the global env if
     no goals are focused and the current goal env if 1 goal is
     focused. If >1 goals are focused it throws an exception. *)
  Tac2core.pf_apply @@ fun env sigma ->
  match EConstr.lookup_named id env with
  | exception Not_found -> return A
  | d -> return (B (Context.Named.Declaration.get_type d))

(* **** Abstract custom type *)

(* Now we define a custom type in OCaml, but we do not want to expose its
   representation in Ltac2. *)
type custom2 = int * int

(* The string given to Val.create must be GLOBALLY unique (not just unique to the current plugin).
   If we wanted to be safe we could do [create (plugin_name^":mycustom2")]. *)
let val_custom2 = Tac2dyn.Val.create "mycustom2"

(* the "repr" for our custom values *)
let custom2 = repr_ext val_custom2

(* a couple toy functions *)
let () = define "mk_custom2" (int @-> int @-> ret custom2) @@ fun i j ->
  (i, j)

let () = define "sum2" (custom2 @-> ret int) @@ fun (i,j) ->
  i + j

(* we can also declare a printer for our custom values. *)

(* Ltac2 printers are type-directed, so we need to tell which type we know how to print.
   The type is identified by its nma of type [Tac2expr.type_constant = KerName.t].
   Current APIs for this are not very nice, we have to write module paths by hand. *)

(* the loader module is a file whose logical name is Tuto4.Loader *)
let loader_module_name = ModPath.MPfile (DirPath.make @@ List.map Id.of_string ["Loader"; "Tuto4"])

(* the type in that module is "custom2" *)
let custom2_type_name = KerName.make loader_module_name (Label.of_id @@ Id.of_string "custom2")

(* the printing system gives us the current env and evar map, the
   value to be printed, and the type arguments at which we are printing. *)
let pr_custom2 env sigma v tys =
  assert (CList.is_empty tys); (* Since custom2 has no arguments, tys is the empty list. *)
  (* by typing, v must be a custom2 value *)
  let (i, j) = repr_to custom2 v in
  (* NB: open Pp would shadow "v" if we did it between binding "v" and using it *)
  let open Pp in
  int i ++ str "," ++ int j

(* Finally, we register our printer for custom2 to be used in Ltac2.
   It will be used every time Ltac2 needs to output values of type custom2. *)
let () = Tac2print.register_val_printer custom2_type_name { val_printer = pr_custom2 }

(* The end of Demo.v show how Ltac2 will use this printer function
   whenever it needs to print a value of type custom2. *)
