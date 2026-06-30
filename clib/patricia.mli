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

(**An integer key. *)
type key =
  int

(**A map. *)
type 'a t

(**The empty map. *)
val empty: 'a t

(**[is_empty m] determines whether the map [m] is empty, that is,
   whether its cardinal is 0. *)
val is_empty: 'a t -> bool

(**[singleton k v] returns a map containing just a binding of the key [k] to
   the value [v]. *)
val singleton: key -> 'a -> 'a t

(**[is_singleton m] determines whether the map [m] is a singleton map,
   that is, whether its cardinal is 1. *)
val is_singleton: 'a t -> bool

(**[add k v m] returns a map whose bindings are all bindings in the map [m]
   plus a binding of the key [k] to the value [v]. If a binding already exists
   for the key [k] then it is overridden. *)
val add: key -> 'a -> 'a t -> 'a t

(**[mem k m] determines whether the map [m] contains a binding of the key [k]
   to some value. *)
val mem: key -> 'a t -> bool

(**[find k m] finds the value associated to the key [k] in the map [m]. If the
   map [m] contains no binding for the key [k] then [Not_found] is raised. *)
val find: key -> 'a t -> 'a

(**[remove k m] is the map [m] deprived from any binding for [k]. *)
val remove: key -> 'a t -> 'a t

(**[find_and_remove k m] finds the value [v] associated to the key [k] in the
   map [m] and returns a pair of the value [v] and the map [remove k m]. If
   the map [m] contains no binding for the key [k] then [Not_found] is
   raised. *)
val find_and_remove: key -> 'a t -> 'a * 'a t

(**[union m1 m2] returns the union of the maps [m1] and [m2]. If a key [k]
   appears in [m1] and in [m2] then its binding in [m2] is retained. *)
val union: 'a t -> 'a t -> 'a t

(**If the map [m] is nonempty then [choose m] returns an arbitrarily chosen
   binding in [m]. Otherwise, [Not_found] is raised. *)
val choose: 'a t -> key * 'a

(**[cardinal m] returns the cardinal of the map [m], that is, the number of
   bindings in the map [m]. *)
val cardinal: 'a t -> int

(**[iter yield m] enumerates the bindings in the map [m] in increasing order
   of keys. *)
val iter: (key -> 'a -> unit) -> 'a t -> unit

(**[fold yield m s] enumerates the bindings in the map [m] in increasing order
   of keys. *)
val fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

(**[fold_rev yield m s] enumerates the bindings in the map [m] in decreasing
   order of keys. *)
val fold_rev: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

(**[bindings m] returns a list of the bindings in the map [m] in increasing
   order of keys. *)
val bindings: 'a t -> (key * 'a) list

(**[exists f m] checks whether at least one binding in the map [m] satisfies
   the predicate [f]. *)
val exists: (key -> 'a -> bool) -> 'a t -> bool

(**[map f] applies the transformation [f] to the values contained in the map
   [m]. *)
val map: ('a -> 'b) -> 'a t -> 'b t

(**[map f] applies the transformation [f] to the bindings contained in
   the map [m]. *)
val mapi: (key -> 'a -> 'b) -> 'a t -> 'b t

(**[filter f m] produces a map containing just the bindings of the map [m]
   that satisfy the predicate [f]. *)
val filter: (key -> 'a -> bool) -> 'a t -> 'a t

(**[equal eq m1 m2] determines whether maps [m1] and [m2] are equal. The
   function [eq] is used to compare the values in the images of the maps. *)
val equal: ('a -> 'b -> bool) -> 'a t -> 'b t -> bool

(**/**)

(**[check] is used for testing only. *)
val check: 'a t -> unit
