(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Uint63 when OCaml integers have less than 63 bits: 32 bits machines,
   js_of_ocaml and wasm_of_ocaml.

   It is Uint63_31 (boxed Int64), but it also accepts the immediate
   integers of the .vo files produced by a 64 bits Rocq, where Uint63.t is
   an int. An immediate is sign extended and masked to 63 bits, which gives
   the value it had on 64 bits. The .vo files of a 64 bits Rocq containing a
   primitive integer which does not fit 31 bits cannot be loaded anyway:
   input_value fails with "integer too large".

   See uint63.ml. *)

module Impl = Uint63_31

type t = Impl.t

let norm (x : t) : t =
  let o = Obj.repr x in
  if Obj.is_int o then Impl.of_int (Obj.obj o) else x

let un f x = f (norm x)
let bin f x y = f (norm x) (norm y)
let ter f x y z = f (norm x) (norm y) (norm z)

let uint_size = Impl.uint_size
let maxuint31 = Impl.maxuint31
let of_int = Impl.of_int
let to_int2 = un Impl.to_int2
let of_int64 = Impl.of_int64
let to_int64 = un Impl.to_int64
let to_int_min x = Impl.to_int_min (norm x)
let of_float = Impl.of_float
let to_float = un Impl.to_float
let hash = un Impl.hash
let to_string = un Impl.to_string
let compile = un Impl.compile
let zero = Impl.zero
let one = Impl.one
let l_sl = bin Impl.l_sl
let l_sr = bin Impl.l_sr
let l_and = bin Impl.l_and
let l_xor = bin Impl.l_xor
let l_or = bin Impl.l_or
let a_sr = bin Impl.a_sr
let add = bin Impl.add
let sub = bin Impl.sub
let mul = bin Impl.mul
let div = bin Impl.div
let rem = bin Impl.rem
let diveucl = bin Impl.diveucl
let divs = bin Impl.divs
let rems = bin Impl.rems
let mulc = bin Impl.mulc
let addmuldiv = ter Impl.addmuldiv
let div21 = ter Impl.div21
let lt = bin Impl.lt
let equal = bin Impl.equal
let le = bin Impl.le
let compare = bin Impl.compare
let lts = bin Impl.lts
let les = bin Impl.les
let compares = bin Impl.compares
let head0 = un Impl.head0
let tail0 = un Impl.tail0
let is_uint63 o = Obj.is_int o || Impl.is_uint63 o
type 'a carry = 'a Impl.carry = C0 of 'a | C1 of 'a
let addc = bin Impl.addc
let addcarryc = bin Impl.addcarryc
let subc = bin Impl.subc
let subcarryc = bin Impl.subcarryc
