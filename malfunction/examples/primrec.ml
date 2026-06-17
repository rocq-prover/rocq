(* Staged compilation of primitive-recursive arithmetic. *)

(* Natural numbers (at type level) *)
type zero = [`Zero]
type 'a suc = [`Suc of 'a]

(* Variables, indexed by the size of the context
  (i.e. number of variables in scope) *)
type _ v =
| ZV : ('a suc) v
| SV : 'a v -> ('a suc) v

(* Well-scoped terms of PRA, with variables as de Bruijn indices.

   PRA includes constants, successor, variables, let, and recursion.
   Recursion defines a function on naturals by giving f 0, and
   f (n + 1) in terms of both n and f n. *)
type 'a t =
| K : int -> 'a t
| S : 'a t -> 'a t
| V : 'a v -> 'a t
| Let : 'a t * ('a suc) t -> 'a t
| Rec : {name : string; ifzero : 'a t; ifsuc : ('a suc suc) t; n : 'a t} -> 'a t


(* less horrible ways of writing de Bruijn indices *)

let v0 = V ZV
let v1 = V (SV ZV)
let v2 = V (SV (SV ZV))
let v3 = V (SV (SV (SV ZV)))
let v4 = V (SV (SV (SV (SV ZV))))

(* Addition, multiplication and exponentiation.
   Bonus points if you can figure out why 'v4' and 'v1' are correct.
   (de Bruijn indices are awful)

   These are eta-expanded with () to get around the value restriction.
   We want them to be polymorphic so that they work in any environment.
   (i.e. we want add () to require at least two variables, not exactly two) *)
let (%) f x = Let(x, f)
let add () = Rec {name = "+"; ifzero = v1; ifsuc = S v1; n = v0}
let mul () = Rec {name = "*"; ifzero = K 0; ifsuc = add () % v4 % v1; n = v0}
let exp () = Rec {name = "^"; ifzero = K 1; ifsuc = mul () % v4 % v1; n = v0}


(* Interpreter for PRA.
   Takes as input a term, and an environment,
   both with the same number of free variables *)

(* Environments, mapping each variable to an integer *)
type _ env =
| Eps : zero env
| Cons : 'a env * int -> ('a suc) env

let rec interpret : type k . k t -> k env -> int =
  fun t env -> match t with
  | K n ->
     n
  | S t ->
     interpret t env + 1
  | V v ->
     let rec lookup : type k . k env -> k v -> int =
       fun env var -> match var, env with
       | ZV, Cons (_env, n) -> n
       | SV v, Cons (env, _) -> lookup env v in
     lookup env v
  | Let (e, body) ->
     let v = interpret e env in
     interpret body (Cons (env, v))
  | Rec {name = _; ifzero; ifsuc; n} ->
     let n = interpret n env in
     let rec go n' fn' =
       if n = n' then fn' else
         let env = Cons (Cons (env, fn'), n') in
         go (n' + 1) (interpret ifsuc env) in
     go 0 (interpret ifzero env)


(* Compiler for PRA. Compare to the interpreter above. *)

(* Environments are split in two:
     Params (variables passed as arguments to the program)
     Locals (variables defined locally with Let) *)
type 'a menv =
| Params : Malfunction.t -> 'a menv
| Local : 'a menv * Malfunction.t -> ('a suc) menv

module I = Malfunction.IntArith
let rec compile : type k . k t -> k menv -> Malfunction.t =
  fun t env -> let open Malfunction in match t with
  | K n ->
     I.of_int n
  | S t ->
     I.(compile t env + one)
  | V v ->
     let rec lookup : type k . k menv -> k v -> Malfunction.t =
       fun env var -> match var, env with
       | ZV, Params env -> Mfield(1, env)
       | SV v, Params env -> lookup (Params (Mfield (0, env))) v
       | ZV, Local (_env, v) -> v
       | SV v, Local (env, _) -> lookup env v in
     lookup env v
  | Let (e, body) ->
     bind_val (compile e env) @@ fun v ->
     compile body (Local (env, v))
  | Rec {name = _; ifzero; ifsuc; n} ->
     bind_val (compile n env) @@ fun n ->
     bind_rec (fun go -> lambda2 @@ fun n' fn' ->
       if_ I.(n = n')
         fn'
         I.(let env = Local(Local(env, fn'), n') in
            Mapply(go, [n' + one; compile ifsuc env]))) @@ fun go ->
     Mapply(go, [I.zero; compile ifzero env])

(* Note that the type of this function is the same as that of 'interpret'
   but partially applying this function will do the compilation work *)

let run_compiled : type k . k t -> k env -> int =
  fun t ->
    let code = Malfunction.(lambda @@ fun v -> compile t (Params v)) in
    let e = Malfunction_compiler.compile_and_load code in
    fun env -> Obj.magic e env


(* testcase: compute 16^4 *)
let _ =
  let env = Cons(Cons(Eps, 16), 4) in
  assert (interpret (exp ()) env = 65536);
  assert (run_compiled (exp ()) env = 65536)

(* benchmark: calculate a bunch of exponents *)
let benchmark name exec =
  let env a b = Cons(Cons(Eps, a), b) in
  (* to ensure same data for both implementations *)
  Random.init 432789;
  let tstart = Unix.gettimeofday () in
  for _ = 1 to 50 do
    let a = Random.int 100 and b = Random.int 5 in
    assert (exec (env a b) = Z.(to_int (pow (of_int a) b)))
  done;
  let tend = Unix.gettimeofday () in
  Printf.printf "%12s: %.2f secs\n%!" name (tend -. tstart)

let _ =
  benchmark "interpreted" (interpret (exp ()));
  benchmark "compiled" (run_compiled (exp ()))

(*
  Results, on my machine:

    interpreted: 5.69 secs
       compiled: 0.18 secs
*)
