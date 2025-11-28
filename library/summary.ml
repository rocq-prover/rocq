(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Stage = struct

type t = Synterp | Interp

let equal x y =
  match x, y with
  | Synterp, Synterp -> true
  | Synterp, Interp -> false
  | Interp, Interp -> true
  | Interp, Synterp -> false

end

let warn_summary_out_of_scope =
  CWarnings.create ~name:"summary-out-of-scope" ~default:Disabled Pp.(fun name ->
      str "A Rocq plugin was loaded inside a local scope (such as a Section)." ++ spc() ++
      str "It is recommended to load plugins at the start of the file." ++ spc() ++
      str "Summary entry: " ++ str name)

module MakeStage(X:sig
    type 'a t
    val get : 'a t -> 'a
    val set : 'a t -> 'b -> 'b t
  end)() = struct
  module Dyn = Dyn.Make()

  let check_name sumname = match Dyn.name sumname with
    | None -> ()
    | Some (Dyn.Any t) ->
      CErrors.anomaly ~label:"Summary.declare"
        Pp.(fmt "Colliding summary names: %s vs %s." sumname (Dyn.repr t))

  type ('v,'freeze,'unfreeze) declaration_gen = {
    freeze : 'v -> 'freeze;
    unfreeze : 'unfreeze -> 'v;
    init : unit -> 'v;
  }

  type ('v,'frozen) declaration = ('v,'frozen,'frozen) declaration_gen

  let generalize_declaration decl = {
    freeze = decl.freeze;
    unfreeze = (fun (_,f) -> decl.unfreeze f);
    init = decl.init;
  }

  module Decl = struct type _ t = D : ('a,'b,('a option * 'b)) declaration_gen -> ('a * 'b) t end
  module DeclMap = Dyn.Map(Decl)

  let sum_map = ref DeclMap.empty

  module Val = struct type _ t = V : 'a -> ('a * _) t end
  module VMap = Dyn.Map(Val)

  type t = VMap.t X.t

  (* option to defend against outdated handles: typically definition
     hooks must not use the handle from when the hook was declared. *)
  type mut = VMap.t option ref X.t

  let fail_outdated_mut() = CErrors.anomaly Pp.(str "leaked outdated mutable summary handle")
  let check_mut x = match !(X.get x) with
    | Some _ -> ()
    | None -> fail_outdated_mut()
  let force_mut x = match !(X.get x) with
    | Some v -> v
    | None -> fail_outdated_mut()
  let get (x:mut) : t = X.set x (force_mut x)
  let set (x:mut) (v:t) : unit = check_mut x; X.get x := Some (X.get v)

  let with_mut (f:mut -> _) (sum:t) : t * _ =
    let sum = X.set sum (ref (Some (X.get sum))) in
    let v = f sum in
    let sumv = get sum in
    X.get sum := None;
    sumv, v

  type 'a v = {
    get : t -> 'a;
    set : mut -> 'a -> unit;
  }

  type 'a tag = Tag : (_ * 'a) Dyn.tag -> 'a tag

  let get_v (type a) (tag:(a * _) Dyn.tag) (x:t) : a =
    match VMap.find tag (X.get x) with
    | exception Not_found -> assert false
    | V v -> v

  let set_v (type a) (tag:(a * _) Dyn.tag) (x:mut) (v:a) : unit =
    let r = X.get x in
    match !r with
    | None -> fail_outdated_mut()
    | Some rv ->
      r := Some (VMap.add tag (V v) rv)

  let make_v (type a) (tag:(a * _) Dyn.tag) : a v = {
    get = get_v tag;
    set = set_v tag;
  }

  type any_summary = AnySummary : (_ * _) Dyn.tag -> any_summary

  let declare_hook = ref None

  let declare_tag_gen sumname decl =
    let () = check_name sumname in
    let tag = Dyn.create sumname in
    let () = sum_map := DeclMap.add tag (D decl) !sum_map in
    let () = Option.iter (fun f -> f (AnySummary tag)) !declare_hook in
    make_v tag, Tag tag

  let declare_tag name decl = declare_tag_gen name (generalize_declaration decl)

  let declare sumname decl = fst @@ declare_tag sumname decl

  let simple_declaration v = {
    freeze = Fun.id;
    unfreeze = Fun.id;
    init = (fun () -> v);
  }

  let declare_simple ~name v = declare name (simple_declaration v)

  let local_declaration v =
    let unfreeze x =
      try CEphemeron.get x
      with CEphemeron.InvalidKey -> v
    in {
      freeze = CEphemeron.create;
      unfreeze;
      init = (fun () -> v);
    }

  let declare_local sumname v = declare sumname (local_declaration v)

  let ref_declaration r =
    let init = !r in {
      freeze = (fun () -> !r);
      unfreeze = (fun x -> r := x);
      init = (fun () -> r := init);
    }

  let ref_tag ~name v =
    let r = ref v in
    let _, tag = declare_tag name (ref_declaration r) in
    r, tag

  let ref ~name v = fst @@ ref_tag ~name v

  let local_ref ~name v =
    let r = Stdlib.ref (CEphemeron.create v) in
    let _ : unit v = declare name (ref_declaration r) in
    let get () = try CEphemeron.get !r with CEphemeron.InvalidKey -> v in
    let set v = r := CEphemeron.create v in
    get,set

  module FrozenVal = struct type _ t = Frozen : 'a -> (_ * 'a) t end
  module FrozenMap = Dyn.Map(FrozenVal)

  module FreezeHMap = Dyn.HMap(Decl)(FrozenVal)

  type frozen = FrozenMap.t

  let empty_frozen = FrozenMap.empty

  let freeze_summaries (x:t) : frozen =
    let x = X.get x in
    let map (type a) (tag:a Dyn.tag) (decl:a Decl.t) : a FrozenVal.t =
      let D decl = decl in
      match VMap.find tag x with
      | exception Not_found ->
          (* XXX not sure if this should be possible *)
          CErrors.anomaly (Pp.fmt "missing summary when freezing: %s" @@ Dyn.repr tag)
      | V v ->
        FrozenVal.Frozen (decl.freeze v)
    in
    FreezeHMap.map { map } !sum_map

  let unfreeze_summaries ?(partial=false) (frozen:frozen) orig =
    (* We must be independent on the order of the map! *)
    let ufz (DeclMap.Any (tag, D decl)) acc =
      let v = match FrozenMap.find tag frozen with
        | Frozen v ->
          let ov = try
              let V v = VMap.find tag orig in
              Some v
            with Not_found -> None
          in
          Some (decl.unfreeze (ov,v))
        | exception Not_found ->
          if not partial then begin
            warn_summary_out_of_scope (Dyn.repr tag);
            Some (decl.init())
          end
          else
            (* critical for stm (playing with removing the evar
               counter from the summary in non_pstate) *)
            None
      in
      match v with
      | None -> acc
      | Some v ->
        VMap.add tag (V v) acc
    in
    DeclMap.fold ufz !sum_map VMap.empty

  let unfreeze_summaries ?partial frozen sum =
    set sum @@ X.set sum @@ unfreeze_summaries ?partial frozen (force_mut sum)

  let init_summaries () =
    let init (DeclMap.Any (tag, D decl)) acc =
      VMap.add tag (V (decl.init())) acc
    in
    DeclMap.fold init !sum_map VMap.empty

  (* XXX interruptions will ruin our day *)
  let capture_new_summaries f =
    assert (Option.is_empty !declare_hook);
    let l = Stdlib.ref [] in
    declare_hook := Some (fun s -> l := s :: !l);
    let v = f() in
    declare_hook := None;
    !l, v

  let init_new_summaries (newsums:any_summary list) (sum:mut) =
    let init (AnySummary tag) =
      let D decl = DeclMap.find tag !sum_map in
      let v = decl.init() in
      set_v tag sum v
    in
    List.iter init newsums

  let init_missing_summaries (sum:mut) =
    let iter (DeclMap.Any (tag, D decl)) =
      if VMap.mem tag (force_mut sum) then ()
      else
        let v = decl.init() in
        set_v tag sum v
    in
    DeclMap.iter iter !sum_map

  let project_from_summary (type a) frozen (Tag tag : a tag) : a =
    let Frozen v = FrozenMap.find tag frozen in
    v

  let modify_summary (type a) frozen (Tag tag : a tag) (x:a) =
    FrozenMap.add tag (Frozen x) frozen

  let remove_from_summary frozen (Tag tag) =
    FrozenMap.remove tag frozen

  let dump = Dyn.dump
end

module Synterp = struct

  module Self = MakeStage(struct
      type 'a t = 'a
      let get x = x
      let set _ y = y
    end)()

  include Self

  type ml_modules = string list

  let sum_mod : (unit,ml_modules) declaration option ref = Stdlib.ref None

  let declare_ml_modules_summary d = sum_mod := Some d

  let freeze_modules () =
    !sum_mod |> Option.map @@ fun decl ->
    decl.freeze ()

  let unfreeze_modules = function
    | None -> ()
    | Some mods ->
    match !sum_mod with
    | None -> CErrors.anomaly Pp.(str "Undeclared ML-MODULES summary.")
    | Some decl -> decl.unfreeze mods

  type frozen = {
    summaries : Self.frozen;
    (** Ordered list w.r.t. the first component. *)
    ml_modules : ml_modules option;
    (** Special handling of the ml_module summary. *)
  }

  let empty_frozen = { summaries = Self.empty_frozen; ml_modules = None }

  let freeze_summaries x =
    let summaries = Self.freeze_summaries x in
    { summaries; ml_modules = freeze_modules () }

  let unfreeze_summaries ?partial { summaries; ml_modules } =
    unfreeze_modules ml_modules;
    unfreeze_summaries ?partial summaries

  let project_from_summary { summaries } tag = Self.project_from_summary summaries tag

  let modify_summary ({ summaries } as frozen) tag v =
    { frozen with summaries = Self.modify_summary summaries tag v }

  let remove_from_summary ({ summaries } as frozen) tag =
    { frozen with summaries = Self.remove_from_summary summaries tag }

end

module Interp = struct

  type 'a with_synterp = { synterp : Synterp.t; interp : 'a }

  module Self = MakeStage(struct
      type 'a t = 'a with_synterp
      let get x = x.interp
      let set x y = { x with interp = y }
    end)()

  type interp_only = Self.VMap.t
  type interp_only_mut = Self.VMap.t option ref

  include Self

  let init_summaries synterp =
    { synterp; interp = Self.init_summaries () }

end

let ref ?(stage=Stage.Interp) ~name x =
  match stage with
  | Interp -> Interp.ref ~name x
  | Synterp -> Synterp.ref ~name x

module StageG = struct

  type (_,_) t =
    | SynterpG : (Synterp.t,Synterp.mut) t
    | InterpG : (Interp.t,Interp.mut) t

  let equal (type a b c d) (s1:(a,b) t) (s2:(c,d) t) : (a * b, c * d) Util.eq option =
    match s1, s2 with
    | SynterpG, SynterpG -> Some Refl
    | InterpG, InterpG -> Some Refl
    | (SynterpG | InterpG), _ -> None
end

let empty = { Interp.synterp = Synterp.Self.VMap.empty; interp = Interp.VMap.empty }

let init () = Interp.init_summaries (Synterp.init_summaries ())

let run_interp interp_f sum =
  let interp = !sum in
  let interp, v =
    Flags.with_modified_ref Flags.in_synterp_phase (fun _ -> Some false) (fun () ->
        Interp.with_mut interp_f interp)
      ()
  in
  sum := interp;
  v

let run_synterp_interp synterp_f interp_f sum =
  let synterp = (!sum).Interp.synterp in
  let synterp, v =
    Flags.with_modified_ref Flags.in_synterp_phase (fun _ -> Some true) (fun () ->
        Synterp.with_mut synterp_f synterp)
      ()
  in
  let interp = { !sum with synterp } in
  let interp, v =
    Flags.with_modified_ref Flags.in_synterp_phase (fun _ -> Some false) (fun () ->
        Interp.with_mut (fun interp -> interp_f interp v) interp)
        ()
  in
  sum := interp;
  v
