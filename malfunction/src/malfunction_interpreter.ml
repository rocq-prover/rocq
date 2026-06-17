open Malfunction

type value =
| Block of int * value array
| Vec of vector_type * value array
| Func of (value -> value)
| Int of inttype * Z.t
| Float of float
| Thunk of value Lazy.t

exception Error of string

let fail fmt =
  let k _ppf =
    raise (Error (Format.flush_str_formatter ())) in
  Format.kfprintf k Format.str_formatter ("@[" ^^ fmt ^^ "@]")

type op_normal = [`Add|`Sub|`Mul|`Div|`Mod|`And|`Or|`Xor]
type op_shift = [`Lsl|`Lsr|`Asr]
type op_cmp = [`Lt|`Gt|`Lte|`Gte|`Eq]

let bitwidth = function
  | `Int -> Sys.word_size - 1
  | `Int32 -> 32
  | `Int64 -> 64

let truncate ty n =
  Int (ty, match ty with
  | `Bigint -> n
  | (`Int|`Int32|`Int64) as ty ->
     let width = bitwidth ty in
     let range = Z.(shift_left (of_int 1) width) in
     let masked = Z.(logand n (sub range (of_int 1))) in
     let min_int = Z.(shift_right range 1) in
     if Z.lt masked min_int then masked else
       Z.(sub masked range)) (* two's complement *)

let as_ty ty = function
  | Int (ty', n) ->
     if ty = ty' then n else fail "integer type mismatch"
  | _ -> fail "expected integer"

let as_float = function
  | Float f -> f
  | _ -> fail "expected float64"

let rec interpret locals env : t -> value = function
  | Mvar v -> Ident.Map.find v locals
  | Mlambda (xs, e) ->
     let (x, e) = match xs with
       | [] -> assert false
       | [x] -> x, e
       | (x :: xs) -> x, Mlambda (xs, e) in
     Func (fun v -> interpret (Ident.Map.add x v locals) env e)
  | Mapply (f, vs) ->
     List.fold_left (fun f v -> match f with
     | Func f -> f (interpret locals env v)
     | _ -> fail "not a function") (interpret locals env f) vs
  | Mlet (bindings, body) ->
     let rec bind locals = function
       | [] ->
          interpret locals env body
       | `Unnamed e :: bindings ->
          ignore (interpret locals env e);
          bind locals bindings
       | `Named (x, e) :: bindings ->
          let locals = Ident.Map.add x (interpret locals env e) locals in
          bind locals bindings
       | `Recursive recs :: bindings ->
          let n = List.length recs in
          let values = Array.make n None in
          let locals = List.fold_right
            (fun (x, e) locals -> Ident.Map.add x e locals)
            (List.mapi (fun i (x, e) ->
              let v = match e with
                | Mlambda _ -> Func (fun arg ->
                    match values.(i) with
                    | Some (Func f) -> f arg
                    | _ -> fail "bad recursive function binding")
                | Mlazy _ -> Thunk (lazy (
                    match values.(i) with
                    | Some (Thunk t) -> Lazy.force t
                    | _ -> fail "bad recursive lazy binding"))
                | _ -> fail "recursive values must be functions or lazy" in
              (x, v)) recs)
            locals in
          recs |> List.iteri (fun i (_, e) ->
            values.(i) <- Some (interpret locals env e));
          bind locals bindings in
     bind locals bindings
  | Mnum (`Int n) -> Int (`Int, Z.of_int n)
  | Mnum (`Int32 n) -> Int (`Int32, Z.of_int32 n)
  | Mnum (`Int64 n) -> Int (`Int64, Z.of_int64 n)
  | Mnum (`Bigint n) -> Int (`Bigint, n)
  | Mnum (`Float64 f) -> Float f
  | Mstring s ->
     Vec (`Bytevec,
          Array.init (String.length s) (fun i -> Int (`Int, Z.of_int (Char.code (String.get s i)))))
  (* These primitives are supported as a hack for testing. See prim.test *)
  | Mglobal (Ldot (Lident "Stdlib", "**")) ->
     Func (function Float a -> Func (function Float b -> Float (a ** b)
                                            | _ -> fail "**: expected float")
                  | _ -> fail "**: expected float")
  | Mglobal (Ldot (Lident "Obj", "magic")) ->
     Func (fun x -> x)
  | Mglobal _v -> fail "globals unsupported"
     (*
     let (path, _descr) = Env.lookup_value v env in
     let path = Env.normalize_path None env path in
     let rec lookup = let open Path in function
       | Pident id -> Symtable.get_global_value id
       | Pdot (path, _, i) -> Obj.field (lookup path) i
       | Papply _ -> fail "functor application in global reference" in
     lookup path
     *)
  | Mswitch (scr, cases) ->
     let scr = interpret locals env scr in
     let rec find_match = function
       | (cases, e) :: rest ->
          if List.exists (fun case -> match case, scr with
          | `Tag n, Block (n', _) -> n = n'
          | `Deftag, Block _ -> true
          | `Intrange (min, max), Int (`Int, n) -> min <= Z.to_int n && Z.to_int n <= max
          | _, _ -> false) cases then
            interpret locals env e
          else
            find_match rest
       | [] -> fail "no case matches" in
     find_match cases
  | Mnumop1 (op, (#inttype as ty), e) ->
     let n = as_ty ty (interpret locals env e) in
     truncate ty (match op with `Neg -> Z.neg n | `Not -> Z.lognot n)
  | Mnumop2 (op, (#inttype as ty), e1, e2) ->
     let e1 = interpret locals env e1 in
     let e2 = interpret locals env e2 in
     begin match op with
     | #op_normal as op ->
        let f = Z.(match op with
          | `Add -> add | `Sub -> sub
          | `Mul -> mul | `Div -> div | `Mod -> rem
          | `And -> logand | `Or -> logor | `Xor -> logxor) in
        truncate ty (f (as_ty ty e1) (as_ty ty e2))
     | #op_shift as op ->
        let n = as_ty ty e1 in
        let c = Z.to_int (as_ty `Int e2) in
        let () = match ty with
          | `Bigint -> ()
          | (`Int|`Int32|`Int64) as ty ->
             let w = bitwidth ty in
             if c < 0 || c >= w then
               fail "invalid shift count %d" c in
        truncate ty Z.(match op with
        | `Lsl -> shift_left n c
        | `Asr -> shift_right n c
        | `Lsr ->
           let n = match ty with
             | `Bigint -> n
             | (`Int|`Int32|`Int64) as ty ->
                let w = bitwidth ty in
                Z.(logand n (sub (shift_left one w) one)) in
           shift_right n c)
     | #op_cmp as op ->
        let cmp = Z.compare (as_ty ty e1) (as_ty ty e2) in
        let res = match op with
          | `Lt -> cmp < 0
          | `Gt -> cmp > 0
          | `Lte -> cmp <= 0
          | `Gte -> cmp >= 0
          | `Eq -> cmp = 0 in
        Int (`Int, if res then Z.one else Z.zero)
     end
  | Mnumop1 (`Neg, `Float64, e) ->
     Float (-. (as_float (interpret locals env e)))
  | Mnumop1 (`Not, `Float64, _)
  | Mnumop2 (#binary_bitwise_op, `Float64, _, _) ->
     failwith "invalid bitwise float operation"
  | Mnumop2 ((#binary_arith_op | #binary_comparison as op),
             `Float64, e1, e2) ->
     let e1 = as_float (interpret locals env e1) in
     let e2 = as_float (interpret locals env e2) in
     begin match op with
     | #binary_arith_op as op ->
        Float (match op with
          | `Add -> e1 +. e2
          | `Sub -> e1 -. e2
          | `Mul -> e1 *. e2
          | `Div -> e1 /. e2
          | `Mod -> mod_float e1 e2)
     | #binary_comparison as op ->
        let res = match op with
          | `Lt -> e1 < e2
          | `Gt -> e1 > e2
          | `Lte -> e1 <= e2
          | `Gte -> e1 <= e2
          | `Eq -> e1 = e2 in
        Int (`Int, if res then Z.one else Z.zero)
     end
  | Mconvert ((#inttype as src), (#inttype as dst), e) ->
     truncate dst (as_ty src (interpret locals env e))
  | Mconvert ((#inttype as src), `Float64, e) ->
     Float (Z.to_float (as_ty src (interpret locals env e)))
  | Mconvert (`Float64, (#inttype as dst), e) ->
     (* FIMXE: ? *)
     truncate dst (Z.of_float (as_float (interpret locals env e)))
  | Mconvert (`Float64, `Float64, e) ->
     Float (as_float (interpret locals env e))
  | Mvecnew (ty, len, def) ->
     (match ty, interpret locals env len, interpret locals env def with
     | `Array, Int (`Int, len), v ->
        Vec (`Array, Array.make (Z.to_int len) v)
     | `Bytevec, Int (`Int, len), (Int (`Int, k) as v) when 0 <= (Z.to_int k) && (Z.to_int k) < 256 ->
        Vec (`Bytevec, Array.make (Z.to_int len) v)
     | _, _, _ -> fail "bad vector creation")
  | Mvecget (ty, vec, idx) ->
     (match interpret locals env vec, interpret locals env idx with
     | Vec (ty', vals), Int (`Int, i) when ty = ty' ->
        let i = Z.to_int i in
        if 0 <= i && i < Array.length vals then
          vals.(i)
        else
          fail "index out of bounds: %d" i
     | _ -> fail "wrong vector type")
  | Mvecset (ty, vec, idx, e) ->
     (match interpret locals env vec,
            interpret locals env idx,
            interpret locals env e with
     | Vec (ty', vals), Int (`Int, i), v when ty = ty' ->
        let i = Z.to_int i in
        if 0 <= i && i < Array.length vals then begin
          (match ty, v with
          |  `Array, _ -> ()
          | `Bytevec, Int (`Int, i) when 0 <= Z.to_int i && Z.to_int i < 256 -> ()
          | `Bytevec, _v -> fail "not a byte");
          vals.(i) <- v; Int (`Int, Z.of_int 0)
        end else
          fail "index out of bounds: %d" i
     | _ -> fail "wrong vector type")
  | Mveclen (ty, vec) ->
     (match interpret locals env vec with
     | Vec (ty', vals) when ty = ty' -> Int (`Int, Z.of_int (Array.length vals))
     | _ -> fail "wrong vector type")
  | Mblock (tag, vals) ->
     Block (tag, Array.of_list (List.map (interpret locals env) vals))
  | Mfield (idx, b) ->
     (match interpret locals env b with
     | Block (_, vals) -> vals.(idx)
     | _ -> fail "not a block")
  | Mlazy e ->
    Thunk (lazy (interpret locals env e))
  | Mforce e ->
     (match interpret locals env e with
      | Thunk (lazy v) -> v
      | _ -> fail "not a lazy value")

let eval exp =
  interpret Ident.Map.empty () exp

let loc =
  let l = Lexing.{pos_fname="<value>"; pos_lnum=0; pos_cnum=0; pos_bol=0} in
  l,l

let rec render_value = let open Malfunction_sexp in function
| Block (tag, elems) -> loc, List (
  (loc, Atom "block")::
  (loc, List [loc, Atom "tag"; loc, Atom (string_of_int tag)])::
  List.map render_value (Array.to_list elems))
| Vec (ty, vals) ->
  loc, List ((loc, Atom (match ty with `Array -> "vector" | `Bytevec -> "vector.byte"))::
              List.map render_value (Array.to_list vals))
| Func _ ->
  loc, Atom "<function>"
| Thunk _ ->
  loc, Atom "<lazy value>"
| Int (ty, n) ->
   let ty = match ty with
     | `Int -> ""
     | `Int32 -> ".i32"
     | `Int64 -> ".i64"
     | `Bigint -> ".ibig" in
   loc, Atom (Z.to_string n ^ ty)
| Float f ->
   let s = match classify_float f with
     | FP_nan -> "nan"
     | FP_infinite -> if f < 0. then "neg_infinity" else "infinity"
     | _ -> string_of_float f in
   loc, Atom s
