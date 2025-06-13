open Names
open Ltac2_plugin
open Tac2externals
open Tac2ffi

(* convenience alias *)
let return = Proofview.tclUNIT

(* used to distinguish our primitives from some other plugin's primitives
   by convention matches the plugin's ocamlfind name *)
let plugin_name = "rocq-plugin-tutorial.tuto4"

let pname s = { Tac2expr.mltac_plugin = plugin_name; mltac_tactic = s }

(* convenience wrapper around Tac2externals.define *)
let define s = define (pname s)

(* a simple function taking an integer and returning a boolean
   "@->" is an infix function from Tac2externals combining "type representation" (Tac2ffi.repr)
   "ret" means we return the answer without doing tactic operations (no access to the Proofview monad) *)
let () = define "the_question" (int @-> ret bool) @@ fun i ->
  Int.equal i 42

(* a wrapper around "exact", it takes a constr (ie a term) and returns nothing
   "tac" means we have access to the tactic monad *)
let () = define "my_exact" (constr @-> tac unit) @@ fun c ->
  Tactics.exact_check c

(** **** Transparent custom type *)

(* We define a custom type in ocaml and in ltac2 (this is the ocaml side) *)
type my_custom =
  | A
  | B of EConstr.t

(* translate from ocaml to the ltac2 representation (Tac2val.valexpr)
   we use Tac2ffi.of_constr in the B case *)
let of_custom = function
  | A -> of_int 0
  | B c -> of_block (0, [|of_constr c|])

(* Go from the ltac2 representation to the ocaml representation.
   This needs to look at the low-level valexpr data.
   If an external is declared with an incorrect Ltac2 type it may be passed invalid values,
   in which case we assert false. *)
let to_custom = let open Tac2val in function
  | ValInt 0 -> A
  | ValBlk (0, [|c|]) -> B (to_constr c)
  | _ -> assert false

(* package the translations into a Tac2ffi.repr *)
let custom = make_repr of_custom to_custom

(* A function returning true if passed [A] or [B] of some inductive type.
   We need the evar map to inspect the term in the B case,
   but we don't need the current goal's hypotheses, so we use "eret"
   (in fact we don't use the env at all).
*)
let () = define "is_ind_or_a" (custom @-> eret bool) @@ fun v env sigma ->
  match v with
  | A -> true
  | B c -> EConstr.isInd sigma c

(* a function returning [A] if the ident is not an hypothesis,
   or [B t] where [t] is its type if it is.

   Since we need to look at the goal to check hypotheses, we use [tac]
   which gives use full access to the proofview monad.

   We could also use "gret", but that fails when 0 goals are focused.
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

(* We define a custom type in ocaml, but do not expose its representation in ltac2 *)
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


let () = Tac2print.register_val_printer custom2_type_name { val_printer = pr_custom2 }
