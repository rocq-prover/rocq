(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Partition refinement algorithm *)

module type PartitionS =
sig
  type t
  (** Type of partition structure *)

  type set
  (** Type of partitions *)

  val create : int -> t
  (** Create a partition structure of the given size *)

  val length : t -> int
  (** Number of partitions *)

  val size : set -> t -> int
  (** Number of elements of a partition *)

  val partition : int -> t -> set
  (** [partition i t] returns the index of the partition which contains [i] *)

  val iter : set -> (int -> unit) -> t -> unit
  (** Iter on elements of a partition. Don't [mark] and [split] in the loop! *)

  val fold : set -> (int -> 'a -> 'a) -> t -> 'a -> 'a
  (** Fold left to right on elements of a partition. Don't [mark] and [split] in
      the loop! *)

  val iter_all : (set -> unit) -> t -> unit
  (** Iter on partitions. Don't [mark] and [split] in the loop! *)

  val fold_all : (set -> 'a -> 'a) -> t -> 'a -> 'a
  (** Fold left to right on partitions. Don't [mark] and [split] in the loop! *)

  val mark : int -> t -> unit
  (** Mark an element for splitting *)

  val split : set -> t -> set
  (** Performs splitting and return the set of marked elements *)

  val is_marked : set -> t -> bool
  (** Returns [true] if some element of the set is marked *)

  val is_valid : set -> bool
  (** Test whether a splitting succeeded *)

  val represent : set -> int
  (** Associate a unique number to each partition. If the partition is valid, then
      the returned number is guaranteed to be between [0] and [len - 1] when
      [len] is the number of partitions of the structure. *)
end

module Partition =
struct

type set = int

type t = {
  mutable partitions : int;
  (** number of partitions *)
  mutable first : int array;
  (** index of the first element of a partition *)
  mutable last : int array;
  (** successor index of the last element of a partition *)
  mutable marked : int array;
  (** index of the last marked element of a partition *)
  index : set array;
  (** associate a partition to an element *)
  elements : int array;
  (** contain elements in a contiguous way w.r.t. partitions *)
  location : int array;
  (** keep the location of an element in [elements] *)
}

let initial_size n = max (n / 100) 7

let create n = {
  partitions = 0;
  first = Array.make (initial_size n) 0;
  last = Array.make (initial_size n) n;
  marked = Array.make (initial_size n) 0;
  index = Array.make n 0;
  elements = Array.init n (fun i -> i);
  location = Array.init n (fun i -> i);
}

let uget (t : int array) i = Array.get t i
let uset (t : int array) i x = Array.set t i x

let length t = succ t.partitions

let size s t =
  uget t.last s - uget t.first s

let partition i t = uget t.index i

let iter s f t =
  let fst = uget t.first s in
  let lst = uget t.last s in
  for i = fst to lst - 1 do
    f (uget t.elements i);
  done

let fold s f t accu =
  let fst = uget t.first s in
  let lst = uget t.last s in
  let rec fold accu i =
    if lst <= i then accu
    else fold (f (uget t.elements i) accu) (succ i)
  in
  fold accu fst

let iter_all f t =
  for i = 0 to t.partitions do f i; done

let fold_all f t accu =
  let rec fold accu i =
    if t.partitions <= i then accu
    else fold (f i accu) (succ i)
  in
  fold accu 0

let resize t =
  let len = Array.length t.first in
  if len <= t.partitions then begin
    let nlen = 2 * len + 1 in
    let pfirst = t.first in
    let plast = t.last in
    let pmarked = t.marked in
    let nfirst = Array.make nlen 0 in
    let nlast = Array.make nlen 0 in
    let nmarked = Array.make nlen 0 in
    for i = 0 to pred len do
      uset nfirst i (uget pfirst i);
      uset nlast i (uget plast i);
      uset nmarked i (uget pmarked i);
    done;
    t.first <- nfirst;
    t.last <- nlast;
    t.marked <- nmarked;
  end

let split s t =
  if uget t.marked s = uget t.last s then uset t.marked s (uget t.first s);
  if uget t.marked s = uget t.first s then -1
  (* Nothing to split *)
  else begin
    let len = succ t.partitions in
    t.partitions <- len;
    resize t;
    uset t.first len (uget t.first s);
    uset t.marked len (uget t.first s);
    uset t.last len (uget t.marked s);
    uset t.first s (uget t.marked s);
    for i = uget t.first len to pred (uget t.last len) do
      uset t.index (uget t.elements i) len;
    done;
    len
  end

let mark i t =
  let set = uget t.index i in
  let loc = uget t.location i in
  let mark = uget t.marked set in
  if mark <= loc then begin
    uset t.elements loc (uget t.elements mark);
    uset t.location (uget t.elements loc) loc;
    uset t.elements mark i;
    uset t.location i mark;
    uset t.marked set (succ mark);
  end

let is_marked s t = (uget t.marked s) <> (uget t.first s)

let is_valid s = 0 <= s

let represent s = s

end

(** Hopcroft algorithm *)

module type S =
sig
  type label
  type state
  type transition = {
    src : state;
    lbl : label;
    dst : state;
  }

  type automaton = {
    states : int;
    partitions : state list list;
    transitions : transition list;
  }

  val reduce : automaton -> state list array
end

module Make (Label : Map.OrderedType) : S
  with type label = Label.t
  and type state = int =
struct

type label = Label.t
type state = int

type transition = {
  src : state;
  lbl : label;
  dst : state;
}

module TMap = Map.Make(Label)

type automaton = {
  states : int;
  partitions : state list list;
  transitions : transition list;
}

(** Partitions of states *)
module SPartition : PartitionS = Partition

(** Partitions of transitions *)
module TPartition : PartitionS = Partition

type environment = {
  state_partition : SPartition.t;
  splitter_partition : TPartition.t;
  transition_source : int array;
}

(** Associate the list of transitions ending in a given state *)
let reverse automaton =
  let ans = Array.make automaton.states [] in
  let add (x : int) l = (* if List.mem x l then l else *) x :: l in
  let iter i trans =
    let l = Array.get ans trans.dst in
    Array.set ans trans.dst (add i l)
  in
  let () = List.iteri iter automaton.transitions in
  ans

let init automaton =
  let transitions = automaton.transitions in
  let len = List.length transitions in
  (* Sort transitions according to their label *)
  let env = {
    state_partition = SPartition.create automaton.states;
    splitter_partition = TPartition.create len;
    transition_source = Array.make len (-1);
  } in
  (* Set the source of the transitions *)
  let iteri i trans = env.transition_source.(i) <- trans.src in
  let () = List.iteri iteri transitions in
  (* Split splitters according to their label *)
  let fold i accu trans = match TMap.find_opt trans.lbl accu with
  | None -> TMap.add trans.lbl [i] accu
  | Some l -> TMap.add trans.lbl (i :: l) accu
  in
  let lblmap = CList.fold_left_i fold 0 TMap.empty transitions in
  let p = env.splitter_partition in
  let pt = TPartition.partition 0 p in
  let iter _ trs =
    let iter idx = TPartition.mark idx p in
    let () = List.iter iter trs in
    ignore (TPartition.split pt p : TPartition.set)
  in
  let () = TMap.iter iter lblmap in
  (* Push every splitter in the todo stack *)
  let fold pt todo = pt :: todo in
  let splitter_todo = TPartition.fold_all fold env.splitter_partition [] in
  env, splitter_todo, automaton.partitions

let split_partition s inv env todo =
  let p = env.state_partition in
  let r = SPartition.split s p in
  if SPartition.is_valid r then begin
    let r = if SPartition.size r p < SPartition.size s p then r else s in
    let fold state accu =
      let fold accu trans =
        let pt = TPartition.partition trans env.splitter_partition in
        let accu =
          if TPartition.is_marked pt env.splitter_partition then accu
          else pt :: accu
        in
        let () = TPartition.mark trans env.splitter_partition in
        accu
      in
      List.fold_left fold accu inv.(state)
    in
    let splitter_touched = SPartition.fold r fold p [] in
    let fold_touched todo pt =
      let npt = TPartition.split pt env.splitter_partition in
      if TPartition.is_valid npt then npt :: todo
      else todo
    in
    List.fold_left fold_touched todo splitter_touched
  end else
    todo

let reduce_aux automaton =
  let env, splitter_todo, initial = init automaton in
  let inv = reverse automaton in
  (* Mark every state in each initial partition and split *)
  let ps = SPartition.partition 0 env.state_partition in
  let splitter_todo =
    let separate todo pt =
      let iter state () = SPartition.mark state env.state_partition in
      let () = List.fold_right iter pt () in
      split_partition ps inv env todo
    in
    List.fold_left separate splitter_todo initial
  in
  (* Main loop *)
  let rec loop = function
  | [] -> ()
  | pt :: todo ->
    let fold t state_touched =
      let previous = env.transition_source.(t) in
      let equiv = SPartition.partition previous env.state_partition in
      let state_touched =
        if SPartition.is_marked equiv env.state_partition then state_touched
        else equiv :: state_touched
      in
      let () = SPartition.mark previous env.state_partition in
      state_touched
    in
    let state_touched = TPartition.fold pt fold env.splitter_partition [] in
    let fold_touched todo equiv = split_partition equiv inv env todo in
    let splitter_todo = List.fold_left fold_touched todo state_touched in
    loop splitter_todo
  in
  let () = loop splitter_todo in
  (env, inv)

let reduce automaton =
  let (ans, _) = reduce_aux automaton in
  let mapping = Array.make (SPartition.length ans.state_partition) [] in
  let iter set =
    let pi = SPartition.represent set in
    let iter i =
      let map = Array.get mapping pi in
      Array.set mapping pi (i :: map)
    in
    SPartition.iter set iter ans.state_partition
  in
  let () = SPartition.iter_all iter ans.state_partition in
  mapping

end
