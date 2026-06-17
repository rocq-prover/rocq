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

type block_tag = private int

type case = [`Tag of int | `Deftag | `Intrange of int * int]

val max_tag : block_tag
val tag_of_int : int -> block_tag


type var = Ident.t

(* the argument to fresh does not affect semantics, but can be useful for debugging *)
val fresh : string -> var

type t =
| Mvar of var
| Mlambda of var list * t
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
  [ `Unnamed of t | `Named of var * t | `Recursive of (var * t) list ]

(* generate 'let' and 'let rec' in HOAS style *)
val bind_val : t -> (t -> t) -> t
val bind_rec : (t -> t) -> (t -> t) -> t

(* create a block of tag 0 *)
val tuple : t list -> t

val lambda : (t -> t) -> t
val lambda2 : (t -> t -> t) -> t

val if_ : t -> t -> t -> t

module IntArith : sig
  val zero : t
  val one : t
  val of_int : int -> t
  val (~-) : t -> t
  val lnot : t -> t
  val (+) : t -> t -> t
  val (-) : t -> t -> t
  val ( * ) : t -> t -> t
  val (/) : t -> t -> t
  val (mod) : t -> t -> t
  val (land) : t -> t -> t
  val (lor) : t -> t -> t
  val (lxor) : t -> t -> t
  val (lsl) : t -> t -> t
  val (lsr) : t -> t -> t
  val (asr) : t -> t -> t
  val (<) : t -> t -> t
  val (>) : t -> t -> t
  val (<=) : t -> t -> t
  val (>=) : t -> t -> t
  val (=) : t -> t -> t
end

(* utility function to catch errors from parsing and compilation *)
val with_error_reporting : Format.formatter -> 'a -> (unit -> 'a) -> 'a


