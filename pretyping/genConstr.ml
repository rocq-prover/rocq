(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module D = Dyn.Make()

type ('raw, 'glb) tag = ('raw * 'glb) D.tag

let create name = D.create name

let eq t1 t2 = D.eq t1 t2

let repr tag = D.repr tag

type raw = Raw : ('raw, _) tag * 'raw -> raw

type glb = Glb : (_, 'glb) tag * 'glb -> glb

module Register(M : sig type ('raw, 'glb) t end) = struct

  module V = struct type _ t = V : ('raw, 'glb) M.t -> ('raw * 'glb) t end

  module VMap = D.Map(V)

  let vals = ref VMap.empty

  let mem tag = VMap.mem tag !vals

  let register tag v =
    assert (not @@ mem tag);
    vals := VMap.add tag (V v) !vals

  let find_opt tag =
    try
      let V v = VMap.find tag !vals in
      Some v
    with Not_found -> None

  let get tag =
    try
      let V v = VMap.find tag !vals in
      v
    with Not_found -> assert false

end
