(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Names
open Libnames
open Libobject
open Lib
open Notation_term
open Notationextern

(* Abbreviations. *)

type abbreviation = {
  abbrev_local : Libobject.locality;
  abbrev_pattern : interpretation;
  abbrev_onlyparsing : bool;
  abbrev_user_warns : Globnames.extended_global_reference UserWarn.with_qf option;
  abbrev_activated : bool; (* Not really necessary in practice *)
  abbrev_src : Loc.t option;
}

let abbrev_table =
  Summary.ref (KerName.Map.empty : (full_path * abbreviation) KerName.Map.t)
    ~name:"ABBREVIATIONS"

let add_abbreviation kn sp abbrev =
  abbrev_table := KerName.Map.add kn (sp,abbrev) !abbrev_table

let toggle_abbreviation ~on ~use kn =
  let sp, data = KerName.Map.find kn !abbrev_table in
  if data.abbrev_activated != on then
    begin
      abbrev_table := KerName.Map.add kn (sp, {data with abbrev_activated = on}) !abbrev_table;
      match use with
      | OnlyPrinting -> ()
      | OnlyParsing | ParsingAndPrinting ->
         if on then
           begin
             Nametab.push_abbreviation ?user_warns:data.abbrev_user_warns (Nametab.Until 1) sp kn;
             Nametab.push_abbreviation (Nametab.Exactly 1) sp kn
           end
         else
           Nametab.remove_abbreviation sp kn
    end

let toggle_abbreviations ~on ~use filter =
  KerName.Map.fold (fun kn (sp,abbrev) () ->
      if abbrev.abbrev_activated != on && filter sp abbrev.abbrev_pattern then toggle_abbreviation ~on ~use kn)
  !abbrev_table ()

let is_alias_of_already_visible_name sp = function
  | _,NRef (ref,None) ->
      let (dir,id) = repr_qualid (Nametab.shortest_qualid_of_global Id.Set.empty ref) in
      DirPath.is_empty dir && Id.equal id (basename sp)
  | _ ->
      false

let load_abbreviation i ((sp,kn),abbrev) =
  if Nametab.exists_cci sp then
    user_err
      (Id.print (basename sp) ++ str " already exists.");
  add_abbreviation kn sp abbrev;
  Nametab.push_abbreviation ?user_warns:abbrev.abbrev_user_warns (Nametab.Until i) sp kn;
  abbrev.abbrev_src |> Option.iter (fun loc -> Nametab.set_cci_src_loc (Abbrev kn) loc);
  let pat = abbrev.abbrev_pattern in
  let () = if not abbrev.abbrev_onlyparsing &&
              abbrev.abbrev_local <> Export &&
              not (Int.equal i 1 && is_alias_of_already_visible_name sp pat) then
      Notationextern.declare_uninterpretation (Global.env ()) (AbbrevRule kn) pat
  in
  ()

let open_abbreviation i ((sp,kn),abbrev) =
  let pat = abbrev.abbrev_pattern in
  if not (Int.equal i 1 && is_alias_of_already_visible_name sp pat) then begin
    Nametab.push_abbreviation (Nametab.Exactly i) sp kn;
    if not abbrev.abbrev_onlyparsing &&
       Int.equal i 1 &&
       abbrev.abbrev_local <> SuperGlobal then
      Notationextern.declare_uninterpretation (Global.env ()) (AbbrevRule kn) pat
  end

let import_abbreviation i sp kn =
  let _,abbrev = KerName.Map.get kn !abbrev_table in
  open_abbreviation i ((sp,kn),abbrev)

let cache_abbreviation d =
  load_abbreviation 1 d;
  open_abbreviation 1 d

let subst_abbreviation (subst,abbrev) =
  let abbrev_pattern = Notation_ops.subst_interpretation subst abbrev.abbrev_pattern in
  { abbrev with abbrev_pattern }

let classify_abbreviation abbrev =
  if abbrev.abbrev_local = Local then Dispose else Substitute

let inAbbreviation : Id.t -> abbreviation -> obj =
  declare_named_object {(default_object "ABBREVIATION") with
    cache_function = cache_abbreviation;
    load_function = load_abbreviation;
    open_function = filtered_open open_abbreviation;
    subst_function = subst_abbreviation;
    classify_function = classify_abbreviation }

let declare_abbreviation ~local user_warns id ~onlyparsing pat =
  let abbrev = {
    abbrev_local = local;
    abbrev_pattern = pat;
    abbrev_onlyparsing = onlyparsing;
    abbrev_user_warns = user_warns;
    abbrev_activated = true;
    abbrev_src = Loc.get_current_command_loc();
    }
  in
  add_leaf (inAbbreviation id abbrev)

(* Remark: do not check for activation (if not activated, it is already not supposed to be located) *)
let search_abbreviation kn =
  let _,abbrev = KerName.Map.find kn !abbrev_table in
  abbrev.abbrev_pattern

let search_filtered_abbreviation filter kn =
  let _,abbrev = KerName.Map.find kn !abbrev_table in
  let res = filter abbrev.abbrev_pattern in
  res
