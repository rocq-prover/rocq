(******************************************************************************)
(*                                                                            *)
(*                                  Patricia                                  *)
(*                                                                            *)
(*                       François Pottier, Inria Paris                        *)
(*                                                                            *)
(*       Copyright 2025--2025 Inria. All rights reserved. This file is        *)
(*       distributed under the terms of the GNU Library General Public        *)
(*       License, with an exception, as described in the file LICENSE.        *)
(*                                                                            *)
(******************************************************************************)

(* This is an implementation of integer maps using Patricia trees, following
   Chris Okasaki's paper at the 1998 ML Workshop in Baltimore. Only big-endian
   trees are provided. *)

(* -------------------------------------------------------------------------- *)

(* We write every runtime assertion in the form [if debug then assert (...)]
   so it is easy to turn off assertions just by setting [debug] to false. We
   set [debug] to true here (so assertions are enabled while testing) and set
   it to false when exporting to Menhir. *)

let debug = true

(* -------------------------------------------------------------------------- *)

(* Basic operations on integers. *)

let[@inline] lowest_bit x =
  x land (-x)

(* A naive linear-time implementation of [highest_bit], for reference.

let rec naive_highest_bit x =
  let m = lowest_bit x in
  if x = m then m else naive_highest_bit (x - m)

 *)

(* [fill_down s] fills a bit set with 1's, starting at the most significant
   set bit. In other words, it replaces all 0's with 1's, except for the
   leading zeros. *)

let[@inline] fill_down s =
  let s = s lor (s lsr 1) in
  let s = s lor (s lsr 2) in
  let s = s lor (s lsr 4) in
  let s = s lor (s lsr 8) in
  let s = s lor (s lsr 16) in
  let s = s lor (s lsr 32) in (* needed only on 64-bit machines *)
  s

(* A more efficient implementation of [highest_bit]. *)

let[@inline] highest_bit s =
  if debug then assert (s <> 0);
  if s < 0 then min_int else
  (* We proceed as follows. First, we compute [fill_down s], whose bit pattern
     is a nonempty sequence of 0's followed with a nonempty sequence of 1's.
     Then, we negate this pattern: we obtain a nonempty sequence of 1's
     followed with a nonempty sequence of 0's. We use [lowest_bit] to find the
     rightmost 1 bit, and shift it by one towards the right. *)
  lowest_bit (lnot (fill_down s)) lsr 1

(* -------------------------------------------------------------------------- *)

(* Endianness. *)

(* In a big-endian Patricia tree, the key's most significant bits are tested
   first. *)

(* Most of the code is independent of this design choice. The following
   functions are aware of endianness; the rest of the code is not. *)

(* A mask is an integer with a single one bit (i.e. a power of 2). *)

type mask =
  int

(* A debugging aid. *)

let rec is_mask m =
  m = 1 ||
  m <> 0 &&
  m land 1 = 0 &&
  is_mask (m lsr 1)

(* [branching_bit] accepts two distinct integers and returns a mask which
   identifies the first bit where they differ. In the big-endian scheme,
   this is the most significant bit. *)

(* Performing a logical [xor] of [i0] and [i1] yields a bit field where all
   differences between [i0] and [i1] show up as one bits. (There must be at
   least one, since [i0] and [i1] are distinct.) *)

let[@inline] branching_bit (i0 : int) (i1 : int) : mask =
  if debug then assert (i0 <> i1);
  let m = highest_bit (i0 lxor i1) in
  if debug then assert (is_mask m);
  m

(* [mask i m] returns an integer [i'], where all bits that [m] says are
   relevant are identical to those in [i] and all other bits are set to 0. *)

(* In the big-endian scheme, the relevant bits in an integer [i] are those
   found (strictly) to the left of the single 1 bit in the mask [m]. *)

(* [mask i m] keeps the relevant bits and set all other bits to 0. *)

(* Miraculously, if [m] is [min_int] then [mask i m] is zero, as desired. *)

let[@inline] mask (i : int) (m : mask) : int =
  if debug then assert (is_mask m);
  i land (lnot (m lsl 1 - 1))

(* [shorter m1 m2] is [true] iff [m1] describes a shorter prefix than [m2],
   that is, iff [m1] makes fewer bits relevant than [m2]. *)

(* This is the case iff the 1 bit in [m1]
        appears left of the 1 bit in [m2]. *)

(* The test [m2 > 0] eliminates the case where [m2] is [min_int]; in this case
   [m2] is all the way to the left, so not shorter than [m1]. Conversely, the
   test [m1 < 0] accepts the case where [m1] is [min_int]; in this case [m1]
   is all the way to the left, so shorter than [m2] (which is not [min_int]).
   The final test [m1 > m2] covers the case where both [m1] and [m2] are
   nonnegative. *)

(* If we had an unsigned integer comparison, we could use it. *)

let[@inline] shorter (m1 : mask) (m2 : mask) : bool =
  if debug then assert (is_mask m1);
  if debug then assert (is_mask m2);
  m2 > 0 && (m1 < 0 || m1 > m2)

(* [match_prefix k p m] returns [true] if and only if the key [k] has prefix
   [p] up to bit [m].

   Throughout this code, prefixes are in normal form: their irrelevant bits
   are set to zero. This is expressed by the equation [mask p m = p]. *)

let[@inline] match_prefix k p m =
  if debug then assert (is_mask m);
  if debug then assert (mask p m = p);
  mask k m = p

(* -------------------------------------------------------------------------- *)

(* Patricia trees represent maps whose keys are integers. *)

type key =
  int

(* A tree is either empty, or a leaf node, containing both the integer key and
   a piece of data, or a binary node. A binary node carries an integer value
   and a mask. This integer value is the longest common prefix of the keys in
   this subtree. The mask is the branching bit. It describes the bit that is
   tested at this node. *)

type 'a t =
  | Empty
  | Leaf of int * 'a
  | Branch of int * mask * 'a t * 'a t

(* -------------------------------------------------------------------------- *)

(* Debugging aids. *)

let rec all_keys_have_prefix p m t =
  match t with
  | Empty ->
      true
  | Leaf (key, _) ->
      match_prefix key p m
  | Branch (_, _, t0, t1) ->
      all_keys_have_prefix p m t0 &&
      all_keys_have_prefix p m t1

let rec check_nonempty oldm t =
  match t with
  | Empty ->
      assert false
  | Leaf (_, _) ->
      ()
  | Branch (p, m, t0, t1) ->
      (* [m] is a mask. *)
      assert (is_mask m);
      (* [p] contains no irrelevant bits. *)
      assert (mask p m = p);
      (* All keys in both subtrees have prefix [p]. *)
      assert (all_keys_have_prefix p m t0);
      assert (all_keys_have_prefix p m t1);
      (* The mask [m] is longer than the masks that appear higher up. *)
      (oldm |> Option.iter @@ fun oldm -> assert (shorter oldm m));
      (* Both subtrees are well-formed. *)
      check_nonempty (Some m) t0;
      check_nonempty (Some m) t1

let check t =
  match t with Empty -> () | _ -> check_nonempty None t

(* -------------------------------------------------------------------------- *)

(* Operations. *)

let empty =
  Empty

let[@inline] is_empty t =
  match t with Empty -> true | Leaf _ | Branch _ -> false

let[@inline] singleton k d =
  Leaf (k, d)

let[@inline] is_singleton t =
  match t with Leaf _ -> true | Empty | Branch _ -> false

let rec choose t =
  match t with
  | Empty ->
      raise Not_found
  | Leaf (k, d) ->
      k, d
  | Branch (_, _, t0, _) ->
      choose t0

(* This implementation of [find] takes branches without checking whether the
   key matches the prefix found at the current node. This means that a query
   for a non-existent key is detected only when a leaf is reached, rather than
   higher up in the tree. This strategy is better when queries are expected to
   be successful. *)

let rec find k t =
  match t with
  | Empty ->
      raise Not_found
  | Leaf (k', d) ->
      if k = k' then d else raise Not_found
  | Branch (_, m, t0, t1) ->
      find k (if k land m = 0 then t0 else t1)

let find =
  find

let mem k m =
  try
    let _ = find k m in true
  with Not_found ->
    false

(* [join p0 t0 p1 t1] is a special case of [union]. We assume that the keys in
   the tree [t0] have longest common prefix [p0] and that the keys in the tree
   [t1] have longest common prefix [p1]. Furthermore, we assume that these
   prefixes disagree. Then, no matter how large the trees [t0] and [t1] are,
   we can merge them just by creating a [Branch] node. *)

let[@inline] join p0 t0 p1 t1 =
  if debug then assert (not (is_empty t0));
  if debug then assert (not (is_empty t1));
  if debug then assert (p0 <> p1);
  let m = branching_bit p0 p1 in
  (* The prefixes agree up to bit [m], where the difference appears. *)
  if debug then assert (mask p0 m = mask p1 m);
  (* The union of [t0] and [t1] has longest common prefix [p]. *)
  let p = mask p0 m in
  if debug then assert (all_keys_have_prefix p m t0);
  if debug then assert (all_keys_have_prefix p m t1);
  (* Therefore we must build a node of the form [Branch (p, m, _, _)]. *)
  if p0 land m = 0 then
    Branch (p, m, t0, t1)
  else
    Branch (p, m, t1, t0)

exception Unchanged

let rec add k d t =
  match t with
  | Empty ->
      Leaf (k, d)
  | Leaf (k0, d0) ->
      if k = k0 then
        if d == d0 then raise Unchanged else Leaf (k, d)
      else
        join k (Leaf (k, d)) k0 t
  | Branch (p, m, t0, t1) ->
      if match_prefix k p m then
        if k land m = 0 then
          Branch (p, m, add k d t0, t1)
        else
          Branch (p, m, t0, add k d t1)
      else
        join k (Leaf (k, d)) p t

let[@inline] add k d t =
  try add k d t with Unchanged -> t

let rec cardinal t =
  match t with
  | Empty ->
      0
  | Leaf _ ->
      1
  | Branch (_, _, t0, t1) ->
      cardinal t0 + cardinal t1

let rec remove k t =
  match t with
  | Empty ->
      raise Not_found
  | Leaf (k', _) ->
      if k = k' then Empty else raise Not_found
  | Branch (p, m, t0, t1) ->
      if k land m = 0 then
        match remove k t0 with
        | Empty ->
            t1
        | t0' ->
            Branch (p, m, t0', t1)
      else
        match remove k t1 with
        | Empty ->
            t0
        | t1' ->
            Branch (p, m, t0, t1')

let[@inline] remove key t =
  try remove key t with Not_found -> t

let rec find_and_remove dst k t =
  match t with
  | Empty ->
      raise Not_found
  | Leaf (k', d) ->
      if k = k' then begin
        dst := Some d;
        Empty
      end
      else
        raise Not_found
  | Branch (p, m, t0, t1) ->
      if k land m = 0 then
        match find_and_remove dst k t0 with
        | Empty ->
            t1
        | t0' ->
            Branch (p, m, t0', t1)
      else
        match find_and_remove dst k t1 with
        | Empty ->
            t0
        | t1' ->
            Branch (p, m, t0, t1')

let find_and_remove k t =
  let dst = ref None in
  let t' = find_and_remove dst k t in
  Option.get !dst, t'

let rec union s t =
  match s, t with

  | _, Empty ->
      s
  | Empty, _ ->
      t

  | Leaf (k, d), _ ->
      (* If the key appears on both sides, then [t] must override [s]. *)
      if mem k t then t
      else add k d t
  | Branch _, Leaf (k, d) ->
      add k d s

  | Branch (p, m, s0, s1), Branch (q, n, t0, t1) ->
      if p = q && m = n then

        (* The trees have the same prefix. Merge their subtrees. *)
        let u0 = union s0 t0
        and u1 = union s1 t1 in
        if t0 == u0 && t1 == u1 then t else
        Branch (p, m, u0, u1)

      else if shorter m n && match_prefix q p m then

        (* [q] contains [p]. Merge [t] with a subtree of [s]. *)
        if q land m = 0 then
          let s0' = union s0 t in
          if s0 == s0' then s else
          Branch (p, m, s0', s1)
        else
          let s1' = union s1 t in
          if s1 == s1' then s else
          Branch (p, m, s0, s1')

      else if shorter n m && match_prefix p q n then

        (* [p] contains [q]. Merge [s] with a subtree of [t]. *)
        if p land n = 0 then
          let t0' = union s t0 in
          if t0 == t0' then t else
          Branch (q, n, t0', t1)
        else
          let u1 = union s t1 in
          if t1 == u1 then t else
          Branch (q, n, t0, u1)

      else

        (* The prefixes disagree. *)
        join p s q t

(* If we write [iter] in the most natural way, by traversing a tree
   from left to right, then we find the positive keys first and the
   negative keys later, because the positive keys have sign bit 0
   and the negative keys have sign bit 1. To compensate for this,
   at the outermost layer, we test if the mask is [min_int], which
   is [branching_bit 0 (-1)]. If so, we enumerate the right child
   first and the left child next. *)

let () =
  assert (branching_bit 0 (-1) = min_int)

let rec iter f t =
  match t with
  | Empty ->
      ()
  | Leaf (k, d) ->
      f k d
  | Branch (_, _, t0, t1) ->
      iter f t0;
      iter f t1

let iter f t =
  match t with
  | Empty ->
      ()
  | Leaf (k, d) ->
      f k d
  | Branch (_, m, t0, t1) ->
      if m = min_int
      then (iter f t1; iter f t0)
      else (iter f t0; iter f t1)

let rec fold f t accu =
  match t with
  | Empty ->
      accu
  | Leaf (k, d) ->
      f k d accu
  | Branch (_, _, t0, t1) ->
      fold f t1 (fold f t0 accu)

let fold f t accu =
  match t with
  | Empty ->
      accu
  | Leaf (k, d) ->
      f k d accu
  | Branch (_, m, t0, t1) ->
      if m = min_int
      then fold f t0 (fold f t1 accu)
      else fold f t1 (fold f t0 accu)

let rec fold_rev f t accu =
  match t with
  | Empty ->
      accu
  | Leaf (k, d) ->
      f k d accu
  | Branch (_, _, t0, t1) ->
      fold_rev f t0 (fold_rev f t1 accu)

let fold_rev f t accu =
  match t with
  | Empty ->
      accu
  | Leaf (k, d) ->
      f k d accu
  | Branch (_, m, t0, t1) ->
      if m = min_int
      then fold_rev f t1 (fold_rev f t0 accu)
      else fold_rev f t0 (fold_rev f t1 accu)

let bindings t =
  fold_rev (fun k d bs -> (k, d) :: bs) t []

let rec exists f t =
  match t with
  | Empty ->
      false
  | Leaf (k, d) ->
      f k d
  | Branch (_, _, t0, t1) ->
      exists f t0 || exists f t1

let rec map f t =
  match t with
  | Empty ->
      Empty
  | Leaf (k, d) ->
      Leaf (k, f d)
  | Branch (p, m, t0, t1) ->
      Branch (p, m, map f t0, map f t1)

let rec mapi f t =
  match t with
  | Empty ->
      Empty
  | Leaf (k, d) ->
      Leaf (k, f k d)
  | Branch (p, m, t0, t1) ->
      Branch (p, m, mapi f t0, mapi f t1)

let rec filter f t =
  match t with
  | Empty ->
      Empty
  | Leaf (k, d) ->
      if f k d then t else Empty
  | Branch (_, _, t0, t1) ->
      let t0' = filter f t0
      and t1' = filter f t1 in
      if t0 == t0' && t1 == t1' then t else
      union t0' t1'

let rec equal eq s t =
  match s, t with
  | Empty, Empty ->
      true
  | Leaf (k1, d1), Leaf (k2, d2) ->
      k1 = k2 && eq d1 d2
  | Branch (p, m, s0, s1), Branch (q, n, t0, t1) ->
      p = q && m = n && equal eq s0 t0 && equal eq s1 t1
  | _, _ ->
      false
