(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module type EqType = sig
  type t
  val eq : t -> t -> bool
end

type statistics = {
  num_bindings: int;
  num_buckets: int;
  max_bucket_length: int;
  bucket_histogram: int array
}

module type S = sig
  type elt
  type t
  val create : int -> t
  val clear : t -> unit
  val repr : int -> elt -> t -> elt
  val stats : t -> statistics
end

(* H.t is a representation of hashes as stored within the [hashes]
   array below. We reserve 0 to denote a distinguished 'void' value
   which corresponds to the absence of a key in this position.

   Note: François Pottier's implementation
   ( https://github.com/fpottier/hachis/ ) also contains
   a distinguished 'tomb' value for slots whose key has been removed
   (Hashtbl.remove). For hash-consing we do not need to handle
   explicit removal; we could use tombstones for keys that get erased
   by the GC, but we just leave the hashes around until the next
   resizing or compression.
*)
module H : sig
  type t = private int
  val void : t
  val of_int : int -> t
end = struct
  type t = int
  let void = 0
  let of_int x =
    if x = void then void + 1 else x
end

module Make (E : EqType) =
  struct

  type elt = E.t

  type t = {
    mutable hashes : H.t array;
    mutable keys : elt Weak.t;
    mutable occupation : int;
    mutable mask : int; (* Array.length hashes - 1
      (note: the length must be a power of two) *)
    travel : int ref;
  }

  let create sz =
    (* We need to guarantee that there is always at least one [void]
       slot for search to terminate, so [sz] must be at least 1.
       We also guarantee that sizes are always a power of 2,
       to compute the modulo efficiently. *)
    let sz' = ref 1 in
    while !sz' < sz do sz' := 2 * !sz' done;
    let sz = !sz' in
    {
      hashes = Array.make sz H.void;
      keys = Weak.create sz;
      occupation = 0;
      mask = sz - 1;
      travel = ref 0;
    }

  let clear t =
    Weak.fill t.keys 0 (Weak.length t.keys) None;
    Array.fill t.hashes 0 (Array.length t.hashes) H.void;
    t.occupation <- 0

  let iter f t =
    let len = Array.length t.hashes in
    for i = 0 to len - 1 do
      match Weak.get t.keys i with
      | None -> ()
      | Some hc -> f hc
    done

  let rec locate t k h =
    let i = (h : H.t :> int) land t.mask in
    locate_loop
      ~mask:t.mask ~travel:t.travel
      t.keys k t.hashes h i
  and locate_loop ~mask ~travel keys k hashes h i =
    incr travel;
    let h' = Array.unsafe_get hashes i in
    let i' = (i + 1) land mask in
    if h' <> h then
      if h' = H.void then Error i
      else locate_loop ~mask ~travel keys k hashes h i'
    else
      match Weak.get keys i with
      | Some k' when E.eq k k' -> Ok k'
      | _ ->
        (* When a value has been erased by the GC (case [None]), we must
           keep looking further for another value with the same hash. It
           would be incorrect to treat it as a [void] hash, for the same
           reason that François distinguishes [tomb] from [void]. *)
        locate_loop ~mask ~travel keys k hashes h i'

  let next_sz n = min (2*n) (Sys.max_array_length / 2)

  let resize t =
    let old_capacity = Array.length t.hashes in
    let old_hashes, old_keys = t.hashes, t.keys in
    let new_capacity = next_sz old_capacity in
    let new_mask = new_capacity - 1 in
    let new_hashes, new_keys =
      Array.make new_capacity H.void,
      Weak.create new_capacity
    in
    t.hashes <- new_hashes;
    t.keys <- new_keys;
    t.mask <- new_mask;
    t.occupation <- 0;
    for i = 0 to old_capacity - 1 do
      match Weak.get old_keys i with
      | None -> ()
      | Some k ->
        let h = Array.unsafe_get old_hashes i in
        match locate t k h with
        | Ok _ ->
          failwith "resize: key already in the table?";
        | Error i ->
          t.occupation <- t.occupation + 1;
          Weak.set new_keys i (Some k);
          new_hashes.(i) <- h;
    done

  let compress t =
    let first_void =
      CArray.findi (fun i h -> h = H.void) t.hashes |> Option.get in
    let len = Array.length t.hashes in
    for i = 0 to len - 1 do
      let i = (first_void + i) mod len in
      let h = t.hashes.(i) in
      if h <> H.void then
        match Weak.get t.keys i with
        | None ->
          t.occupation <- t.occupation - 1;
          t.hashes.(i) <- H.void;
        | Some k ->
          match locate t k h with
          | Ok _ -> ()
          | Error j ->
            Weak.set t.keys j (Some k);
            Weak.set t.keys i None;
            t.hashes.(j) <- h;
            t.hashes.(i) <- H.void;
    done

  let[@inline] capacity t =
    t.mask + 1

  let crowded t =
    (* resize at 82% occupation (105/128);
       from François Pottier's [hachis] library. *)
    128 * t.occupation > 105 * capacity t

  let repr h k t =
    let h = H.of_int h in
    if crowded t then begin
      (* Our estimation of occupation does not take into account weak
         keys that have been removed by the GC. When the occupation
         becomes high and we consider resizing, we first loook at
         whether the real occupation is low enough that no resizing is
         necessary -- in this case we just compress the data in-place,
         without moving to larger backing arrays. *)
      let real_occupation =
        let count = ref 0 in
        iter (fun _ -> incr count) t;
        !count
      in
      if real_occupation < capacity t / 2
      then compress t
      else resize t;
      t.travel := 0;
    end
    else if !(t.travel) > 42 * capacity t then begin
      (* In workloads where hits dominate misses, the table grows very
         slowly, so the crowded criterion rarely applies. It remains
         useful to compress it from time to time, to get a chance to
         remove collected values and thus speedup future lookups.

         To compress regularly, we measure the 'travel' caused by
         lookups, the total number of positions they have visited since
         the last resizing or compression. When they have visited many
         times the total size of the structure, we have amortized the
         cost of a compression.

         On [test_qs.ml] from the [ocaml-hashcons] repository (99.8%
         hit rate), this extra source of compression reduces average
         lookup travel from 5.4 to 1.3, and runtime is reduced from 1.7s
         to 1.3s. *)
      compress t;
      t.travel := 0;
    end;
    match locate t k h with
    | Ok k' ->
      k'
    | Error i ->
      Weak.set t.keys i (Some k);
      Array.unsafe_set t.hashes i h;
      t.occupation <- t.occupation + 1;
      k

  let stats t =
    let num_bindings =
      (* number of live keys *)
      let i = ref 0 in iter (fun _ -> incr i) t; !i in
    let interval_lens =
      let voids = ref [] in
      Array.iteri (fun i h -> if h == H.void then voids := i :: !voids) t.hashes;
      let voids = Array.of_list (List.rev !voids) in
      List.init (Array.length voids - 1) (fun i ->
        if i < Array.length voids - 1 then
          voids.(i + 1) - voids.(i) - 1
        else
          Array.length t.hashes - voids.(i) - 1
          + voids.(0)
      )
      |> List.filter ((<>) 0) (* filter out empty gaps *)
      |> Array.of_list
    in
    let nb_intervals = Array.length interval_lens in
    let max_interval_len = interval_lens.(nb_intervals - 1) in
    let histogram =
      let hist = Array.make (max_interval_len + 1) 0 in
      Array.iter (fun l -> hist.(l) <- hist.(l) + 1) interval_lens;
      hist
    in
    {
      num_bindings;
      num_buckets = nb_intervals;
      max_bucket_length = max_interval_len;
      bucket_histogram = histogram;
    }
end

module Combine = struct
    (* These are helper functions to combine the hash keys in a similar
       way as [Hashtbl.hash] does. The constants [alpha] and [beta] must
       be prime numbers. There were chosen empirically. Notice that the
       problem of hashing trees is hard and there are plenty of study on
       this topic. Therefore, there must be room for improvement here. *)
    let alpha = 65599
    let beta  = 7
    let combine x y     = x * alpha + y
    let combine3 x y z   = combine x (combine y z)
    let combine4 x y z t = combine x (combine3 y z t)
    let combine5 x y z t u = combine x (combine4 y z t u)
    let combinesmall x y = beta * x + y
end
