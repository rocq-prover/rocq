type inttype = [`Int | `Int32 | `Int64 | `Bigint]
type numtype = [inttype | `Float64]
type numconst = [`Int of int | `Int32 of Int32.t | `Int64 of Int64.t | `Bigint of Z.t | `Float64 of float]
type unary_num_op =
  [`Neg | `Not]
type binary_arith_op = [ `Add | `Sub | `Mul | `Div | `Mod ]
type binary_bitwise_op = [ `And | `Or | `Xor | `Lsl | `Lsr | `Asr ]
type binary_comparison = [ `Lt | `Gt | `Lte | `Gte | `Eq ]
type binary_num_op =
  [ binary_arith_op | binary_bitwise_op | binary_comparison ]

type vector_type =
  [`Array | `Bytevec]
type mutability =
  [ `Imm | `Mut ]

type block_tag = int

type case = [`Tag of int | `Deftag | `Intrange of int * int]


let max_tag = 200
let tag_of_int n =
  if 0 <= n && n < max_tag then
    n
  else
    invalid_arg "tag out of range"



type t =
| Mvar of Ident.t
| Mlambda of Ident.t list * t
| Mapply of t * t list
| Mlet of binding list * t
| Mnum of numconst
| Mstring of string
| Mglobal of Longident.t
| Mswitch of t * (case list * t) list

(* Numbers *)
| Mnumop1 of unary_num_op * numtype * t
| Mnumop2 of binary_num_op * numtype * t * t
| Mconvert of numtype * numtype * t

(* Vectors *)
| Mvecnew of vector_type * t * t
| Mvecget of vector_type * t * t
| Mvecset of vector_type * t * t * t
| Mveclen of vector_type * t

(* Lazy *)
| Mlazy of t
| Mforce of t

(* Blocks *)
| Mblock of int * t list
| Mfield of int * t

and binding =
  [ `Unnamed of t | `Named of Ident.t * t | `Recursive of (Ident.t * t) list ]


type var = Ident.t

let fresh = Ident.create_local

let bind_val e body =
  let v = fresh "x" in
  Mlet ([`Named (v, e)], body (Mvar v))

let bind_rec e body =
  let v = fresh "x" in
  Mlet ([`Recursive [v, e (Mvar v)]], body (Mvar v))

let tuple xs = Mblock(0, xs)

let lambda f =
  let v = fresh "x" in
  Mlambda ([v], f (Mvar v))

let lambda2 f =
  let vx = fresh "x" and vy = fresh "y" in
  Mlambda ([vx; vy], f (Mvar vx) (Mvar vy))

let if_ c tt ff =
  Mswitch (c, [[`Intrange(0,0)], ff; [`Intrange(min_int,max_int);`Deftag], tt])

module IntArith = struct
  let of_int n = Mnum (`Int n)
  let zero = of_int 0
  let one = of_int 1
  let (~-) a = Mnumop1(`Neg, `Int, a)
  let lnot a = Mnumop1(`Not, `Int, a)
  let (+) a b = Mnumop2(`Add, `Int, a, b)
  let (-) a b = Mnumop2(`Sub, `Int, a, b)
  let ( * ) a b = Mnumop2(`Mul, `Int, a, b)
  let (/) a b = Mnumop2(`Div, `Int, a, b)
  let (mod) a b = Mnumop2(`Mod, `Int, a, b)
  let (land) a b = Mnumop2(`And, `Int, a, b)
  let (lor) a b = Mnumop2(`Or, `Int, a, b)
  let (lxor) a b = Mnumop2(`Xor, `Int, a, b)
  let (lsl) a b = Mnumop2(`Lsl, `Int, a, b)
  let (lsr) a b = Mnumop2(`Lsr, `Int, a, b)
  let (asr) a b = Mnumop2(`Asr, `Int, a, b)
  let (<) a b = Mnumop2(`Lt, `Int, a, b)
  let (>) a b = Mnumop2(`Gt, `Int, a, b)
  let (<=) a b = Mnumop2(`Lte, `Int, a, b)
  let (>=) a b = Mnumop2(`Gte, `Int, a, b)
  let (=) a b = Mnumop2(`Eq, `Int, a, b)
end

let with_error_reporting ppf def f =
  try f () with
  | Malfunction_sexp.SyntaxError ((locstart, locend), msg) ->
     let open Lexing in
     if locstart.pos_lnum = locend.pos_lnum then
       Format.fprintf ppf "%s:%d:%d-%d: %s\n%!"
         locstart.pos_fname locstart.pos_lnum (locstart.pos_cnum - locstart.pos_bol) (locend.pos_cnum - locend.pos_bol) msg
     else
       Format.fprintf ppf "%s:%d:%d-%d:%d %s\n%!"
         locstart.pos_fname locstart.pos_lnum (locstart.pos_cnum - locstart.pos_bol) locend.pos_lnum (locend.pos_cnum - locend.pos_bol) msg;
     def
  | x ->
     Printexc.print_backtrace stdout;
     Location.report_exception ppf x;
    def

