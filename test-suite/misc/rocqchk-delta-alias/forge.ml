(* Forge the .vo files of misc/rocqchk_delta_alias.sh,
   misc/rocqchk_forged_aliases.sh, misc/rocqchk_register_type.sh and
   misc/rocqchk_primitive_operator.sh. The code is deliberately independent
   of Rocq's OCaml libraries: this is an untrusted file producer, not
   another path through the kernel API.

   ocaml forge.ml FILE.vo DONOR.vo constant|inductive
     Replace a declaration in B by an incompatible declaration from another
     compiled copy of the same logical library, while retaining the target's
     resolver that aliases B's declaration to A's.
   ocaml forge.ml parameter|nested|nested-inductive|nested-missing|label
                  LIB.vo OUT.vo
     Record in a delta resolver of LIB.vo an alias that coqc never writes;
     see the function of that name.
   ocaml forge.ml int0 LIB.vo OUT.vo LABEL
     Give the parameter LABEL of LIB.vo the body Int 0, the int63 literal 0.
   ocaml forge.ml head0 LIB.vo OUT.vo LABEL
     Give the parameter LABEL of LIB.vo the body #int63_head0, the primitive
     operator Int63head0.
   ocaml forge.ml register LIB.vo OUT.vo NAME [CANONICAL]
     Register the constant NAME as the int63 primitive type, with the
     canonical name CANONICAL if it is given, which coqc does only for a
     parameter that Primitive declares, under its own name. NAME and
     CANONICAL are full names, such as RegisterType.Lib.M.int, of constants
     that the type or the definition of a constant at the top of LIB.vo
     names.
   ocaml forge.ml client CLIENT.vo LIB.vo LIB_DIRPATH OUT.vo
     Record the digest of LIB.vo as that of the dependency LIB_DIRPATH of
     CLIENT.vo, so that a client compiled against another library loads
     LIB.vo.

   The values read and written are laid out as in checker/values.ml:
   - library segment: (compiled_library, _, _); compiled_library fields 1,
     the root module_body, 4, the dependencies, an array of (dirpath,
     vodigest), a dirpath being a list of identifiers, innermost first, and
     a vodigest Dvo_or_vi (tag 0) [digest of the library segment], and 6,
     the retroknowledge, a list of actions, among them Register_type (tag
     1) [primitive type, PT_int63 being 0; name]; summary segment: field 1,
     the same dependencies;
   - module_body: 1 signature, 3 delta resolver;
     module_type_body: 1 signature; signature: NoFunctor (tag 0) [structure]
     | MoreFunctor (tag 1) [parameter; parameter's type; signature];
     structure: a list of (label, field), a field being SFBconst (tag 0)
     [constant_body], SFBmind (tag 1) [mutual_inductive_body], SFBmodule
     (tag 3) [module_body] or SFBmodtype (tag 4) [module_type_body];
   - constant_body: 2 body, Undef (tag 0) [inline] for a parameter, Def
     (tag 1) [term] for a definition and Primitive (tag 3) [operator,
     Int63head0 being 0], 3 type; term: Prod (tag 6) [binder; domain;
     codomain], App (tag 9) [function; arguments], Const (tag 10)
     [(name, instance)], Ind (tag 11) [((name, index), instance)] or Int
     (tag 17) [63-bit integer, an int on a 64-bit platform and an Int64.t
     on a 32-bit one], among others; name, of a constant or an inductive:
     Same (tag 0) [kernel name] | Dual (tag 1) [user name; canonical name];
     kernel name: [module path; label; hash]; module path: MPfile (tag 0)
     [dirpath] or MPdot (tag 2) [module path; label], among others;
   - delta resolver: field 2, the canonical names, an Int.Map from a kernel
     name's hash to a map from kernel names to kernel names; both are the
     standard library's maps, Empty (0) | Node [left; key; value; right;
     height]. *)

type segment = {
  name : string;
  pos : int64;
  len : int64;
  hash : string;
}

let input_int64 ch =
  let rec go i accu =
    if i = 0 then accu
    else
      go (i - 1)
        (Int64.logor (Int64.shift_left accu 8)
           (Int64.of_int (input_byte ch)))
  in
  go 8 0L

let output_int64 ch n =
  for shift = 7 downto 0 do
    output_byte ch
      (Int64.to_int (Int64.logand 255L (Int64.shift_right_logical n (8 * shift))))
  done

let read_segments ch =
  seek_in ch 8;
  let summary_pos = input_int64 ch in
  LargeFile.seek_in ch summary_pos;
  let n = input_binary_int ch in
  Array.init n (fun _ ->
      let name = really_input_string ch (input_binary_int ch) in
      let pos = input_int64 ch in
      let len = input_int64 ch in
      let hash = really_input_string ch 16 in
      { name; pos; len; hash })

let read_vo file =
  let input = open_in_bin file in
  let header = really_input_string input 8 in
  let contents =
    Array.map
      (fun segment ->
        LargeFile.seek_in input segment.pos;
        segment, really_input_string input (Int64.to_int segment.len))
      (read_segments input)
  in
  close_in input;
  header, contents

let find_segment name contents =
  match Array.find_opt (fun (segment, _) -> String.equal segment.name name) contents with
  | Some found -> found
  | None -> failwith ("missing " ^ name ^ " segment")

(* Write [dst] with the segments of [src], each one named in [edits] replaced
   by its edit of the segment's data. [dst] may be [src]. *)
let rewrite src dst edits =
  let header, contents = read_vo src in
  let temporary = dst ^ ".forged" in
  let output = open_out_bin temporary in
  output_string output header;
  output_int64 output 0L;
  let rewritten =
    Array.map
      (fun (segment, data) ->
        let data =
          match List.assoc_opt segment.name edits with
          | None -> data
          | Some edit -> edit data
        in
        let pos = LargeFile.pos_out output in
        output_string output data;
        let hash = Digest.string data in
        output_string output hash;
        { name = segment.name; pos; len = Int64.of_int (String.length data); hash })
      contents
  in
  let summary_pos = LargeFile.pos_out output in
  output_binary_int output (Array.length rewritten);
  Array.iter
    (fun segment ->
      output_binary_int output (String.length segment.name);
      output_string output segment.name;
      output_int64 output segment.pos;
      output_int64 output segment.len;
      output_string output segment.hash)
    rewritten;
  LargeFile.seek_out output 8L;
  output_int64 output summary_pos;
  close_out output;
  Sys.rename temporary dst

let field v i = Obj.field v i

(* The structure of a module or module type that is not a functor. *)
let struc mb =
  let signature = field mb 1 in
  if Obj.is_int signature || Obj.tag signature <> 0 || Obj.size signature <> 1
  then failwith "unexpected functorized module";
  field signature 0

let find_field name structure =
  let rec loop cell =
    if Obj.is_int cell then failwith ("missing structure field " ^ name)
    else
      let item = field cell 0 in
      let label = field item 0 in
      if not (Obj.is_int label) && Obj.tag label = Obj.string_tag
         && String.equal (Obj.obj label) name
      then field item 1
      else loop (field cell 1)
  in
  loop structure

(* [o] with its field [i] replaced by [f] of it. A value can be shared with
   another part of the file, such as a module's implementation, so [o] is
   copied, not modified, and only when the field changes. *)
let upd i f o =
  let x = field o i in
  let y = f x in
  if y == x then o
  else begin
    let o = Obj.dup o in
    Obj.set_field o i y;
    o
  end

let map_array f a =
  let a = ref a in
  for i = 0 to Obj.size !a - 1 do a := upd i f !a done;
  !a

let block tag fields =
  let b = Obj.new_block tag (Array.length fields) in
  Array.iteri (Obj.set_field b) fields;
  b

let string o : string = Obj.obj o

(* The declaration (constant_body, module_body or module_type_body) of the
   field [name] of a structure, and the structure with that declaration
   replaced by [f] of it. *)
let get name structure = field (find_field name structure) 0

let rec on name f structure =
  if Obj.is_int structure then failwith ("missing structure field " ^ name)
  else if String.equal (string (field (field structure 0) 0)) name then
    upd 0 (upd 1 (upd 0 f)) structure
  else upd 1 (on name f) structure

(* [mb], a module or module type that is not a functor, with its structure
   replaced by [f] of it; the structure of the body of a functor with one
   parameter, and the functor with that structure replaced by [f] of it. *)
let on_struc f = upd 1 (upd 0 f)
let body_struc mb = field (field (field mb 1) 2) 0
let on_body_struc f = upd 1 (upd 2 (upd 0 f))

let typ cb = field cb 3
let definition cb = field (field cb 2) 0

(* [term] with [f] applied to the name of each constant or inductive that it
   names as its head, as an argument of an application or in a product, the
   only places where the files of misc/rocqchk_forged_aliases.sh name the
   declarations read or renamed here. *)
let rec map_names f term =
  if Obj.is_int term then term
  else
    match Obj.tag term with
    | 6 -> term |> upd 1 (map_names f) |> upd 2 (map_names f)
    | 9 -> term |> upd 0 (map_names f) |> upd 1 (map_array (map_names f))
    | 10 -> upd 0 (upd 0 f) term
    | 11 -> upd 0 (upd 0 (upd 0 f)) term
    | _ -> term

(* The user name of the one declaration labelled [label] that [term] names. *)
let named label term =
  let found = ref [] in
  let note name =
    if String.equal (string (field (field name 0) 1)) label then found := field name 0 :: !found;
    name
  in
  let _ = map_names note term in
  match !found with
  | [ kn ] -> kn
  | _ -> failwith ("expected one name labelled " ^ label)

(* [cb] with the name whose user name is [kn], where its type names it,
   replaced by [name]. *)
let rename kn name cb =
  let cb' = upd 3 (map_names (fun n -> if compare (field n 0) kn = 0 then name else n)) cb in
  if cb' == cb then failwith "nothing to rename";
  cb'

let same kn = block 0 [| kn |]
let dual user canonical = block 1 [| user; canonical |]

(* [reso] with the canonical name [canonical] for [user]. The resolvers
   changed here have no canonical names yet, so the result has one bucket
   with one entry. *)
let add_alias user canonical reso =
  let node key value = block 0 [| Obj.repr 0; key; value; Obj.repr 0; Obj.repr 1 |] in
  if Obj.is_block (field reso 2) then failwith "the resolver already has canonical names";
  upd 2 (fun _ -> node (field user 2) (node user canonical)) reso

(* In the type of M2 : TF, M2.c becomes an alias of M1.c, declared in the
   type of M1 : TT: M2's resolver gets the alias, and TF's f : c = false
   names M2.c with the canonical name M1.c. *)
let parameter root =
  let m2c = named "c" (typ (get "f" (struc (get "M2" root)))) in
  let m1c = named "c" (typ (get "e" (struc (get "M1" root)))) in
  on "M2"
    (fun mb ->
      mb
      |> on_struc (on "f" (rename m2c (dual m2c m1c)))
      |> upd 3 (add_alias m2c m1c))
    root

(* A's resolver gets the alias A.X.l -> A.Y.l, which the resolver of A.X,
   under which A.X's fields are checked, does not have. In T and in R's
   signature, e's type names A.Y.l instead of A.X.l. *)
let nested l root =
  let r = struc (get "R" root) in
  let x = named l (typ (get "e" r)) and y = named l (definition (get "c'" r)) in
  let e_y mb = on_struc (on "e" (rename x (same y))) mb in
  root |> on "A" (upd 3 (add_alias x y)) |> on "T" e_y |> on "R" e_y

(* In the body of F (P : S), F.k := P.X.d becomes an alias of P.X.d, from
   label k to label d: F's resolver gets the alias, and lemma : k = false
   names F.k with the canonical name P.X.d. *)
let label root =
  let body = body_struc (get "F" root) in
  let fk = named "k" (typ (get "lemma" body)) and pxd = named "d" (definition (get "k" body)) in
  on "F"
    (fun mb ->
      mb
      |> on_body_struc (on "lemma" (rename fk (dual fk pxd)))
      |> upd 3 (add_alias fk pxd))
    root

let rec strings l = if Obj.is_int l then [] else string (field l 0) :: strings (field l 1)

(* The structure [root] with the body of its parameter [label] replaced by
   [body]. *)
let set_body label body root =
  on label
    (fun cb ->
      let old = field cb 2 in
      if Obj.is_int old || Obj.tag old <> 0 then failwith (label ^ " is not a parameter");
      upd 2 (fun _ -> body) cb)
    root

(* The definition Int 0, of the int63 literal 0. *)
let int0 = block 1 [| block 17 [| if Sys.word_size = 64 then Obj.repr 0 else Obj.repr 0L |] |]

(* The body #int63_head0. *)
let head0 = block 3 [| Obj.repr 0 |]

let rec mp_to_string mp =
  match Obj.tag mp with
  | 0 -> String.concat "." (List.rev (strings (field mp 0)))
  | 2 -> mp_to_string (field mp 0) ^ "." ^ string (field mp 1)
  | _ -> failwith "unexpected module path"

(* The kernel name of the constant [name] that the type or the definition of
   a constant of the structure [root] names. It is taken from the file, hash
   included, never rebuilt. *)
let find_constant name root =
  let found = ref None in
  let note c =
    let kn = field c 0 in
    if String.equal (mp_to_string (field kn 0) ^ "." ^ string (field kn 1)) name then
      found := Some kn;
    c
  in
  let rec loop cell =
    if Obj.is_block cell then begin
      let decl = field (field cell 0) 1 in
      if Obj.tag decl = 0 then begin
        let cb = field decl 0 in
        ignore (map_names note (typ cb));
        let body = field cb 2 in
        if Obj.is_block body && Obj.tag body = 1 then ignore (map_names note (field body 0))
      end;
      loop (field cell 1)
    end
  in
  loop root;
  match !found with
  | Some kn -> kn
  | None -> failwith ("no constant names " ^ name)

(* The compiled library [lib] with the constant [name] registered as the
   int63 type, Register_type [PT_int63; name], with the canonical name
   [canonical] if it is given. *)
let register name canonical lib =
  let root = struc (field lib 1) in
  let user = find_constant name root in
  let cst = match canonical with
    | None -> same user
    | Some c -> dual user (find_constant c root)
  in
  upd 6 (fun retro -> block 0 [| block 1 [| Obj.repr 0; cst |]; retro |]) lib

(* [deps] with [digest] as the digest of the library [dp]. *)
let set_digest dp digest deps =
  let set dep =
    if String.equal (String.concat "." (List.rev (strings (field dep 0)))) dp then
      block 0 [| field dep 0; block 0 [| Obj.repr digest |] |]
    else dep
  in
  let deps' = map_array set deps in
  if deps' == deps then failwith ("no dependency " ^ dp);
  deps'

let marshalled f data = Marshal.to_string (f (Marshal.from_string data 0)) []

let () =
  let forge f = [ "library", marshalled (upd 0 (upd 1 (on_struc f))) ] in
  match List.tl (Array.to_list Sys.argv) with
  | [ "parameter"; src; dst ] -> rewrite src dst (forge parameter)
  | [ ("nested" | "nested-missing"); src; dst ] ->
    rewrite src dst (forge (nested "d"))
  | [ "nested-inductive"; src; dst ] -> rewrite src dst (forge (nested "I"))
  | [ "label"; src; dst ] -> rewrite src dst (forge label)
  | [ "int0"; src; dst; label ] -> rewrite src dst (forge (set_body label int0))
  | [ "head0"; src; dst; label ] -> rewrite src dst (forge (set_body label head0))
  | [ "register"; src; dst; name ] ->
    rewrite src dst [ "library", marshalled (upd 0 (register name None)) ]
  | [ "register"; src; dst; name; canonical ] ->
    rewrite src dst [ "library", marshalled (upd 0 (register name (Some canonical))) ]
  | [ "client"; src; lib; dp; dst ] ->
    let library, _ = find_segment "library" (snd (read_vo lib)) in
    rewrite src dst
      [ "summary", marshalled (upd 1 (set_digest dp library.hash));
        "library", marshalled (upd 0 (upd 4 (set_digest dp library.hash))) ]
  | [ file; donor; ("constant" | "inductive" as mode) ] ->
    let name = if String.equal mode "constant" then "x" else "inhabited" in
    let _, data = find_segment "library" (snd (read_vo donor)) in
    let donor_root = struc (field (field (Marshal.from_string data 0) 0) 1) in
    let decl = get name (struc (get "B" donor_root)) in
    rewrite file file (forge (on "B" (on_struc (on name (fun _ -> decl)))))
  | _ ->
    prerr_endline "usage: see the head of forge.ml";
    exit 2
