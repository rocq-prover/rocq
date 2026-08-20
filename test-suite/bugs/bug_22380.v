Set Universe Polymorphism.
Set Definitional UIP.

Definition flag : bool. Proof. exact true. Qed.

Inductive seq@{i} {A : Type@{i}} (x : A) : A -> SProp :=
| srefl : seq x x.

Definition transport@{i j} {A : Type@{i}} (P : A -> Type@{j})
    {x y : A} (e : seq x y) : P x -> P y :=
  match e in seq _ y return P x -> P y with
  | srefl _ => fun v => v
  end.

Definition certificate@{anchor data out | anchor < out, data < out}
    : Type@{out} :=
  { A : Type@{data} & @eq Type@{out} A Type@{anchor} }.

Definition cert_choice@{anchor data out | anchor < out, data < out}
    : Type@{out} :=
  if flag then certificate@{anchor data out}
  else certificate@{anchor data out}.

Definition cert_inhabitant@{anchor data out | anchor < data, data < out}
    : cert_choice@{anchor data out} :=
  match flag as b return
    (if b then certificate@{anchor data out}
     else certificate@{anchor data out}) with
  | true => @existT (Type@{data})
      (fun A : Type@{data} => @eq Type@{out} A Type@{anchor})
      Type@{anchor} (@eq_refl Type@{out} Type@{anchor})
  | false => @existT (Type@{data})
      (fun A : Type@{data} => @eq Type@{out} A Type@{anchor})
      Type@{anchor} (@eq_refl Type@{out} Type@{anchor})
  end.

Definition cert_force_type@{anchor data out top |
    anchor < data, data < out, out < top} : Type@{out} :=
  let T := (fun _ : unit => cert_choice@{anchor data out}) tt in
  @transport@{top top} Type@{out}
    (fun X : Type@{out} => X -> Type@{out})
    T (if flag then certificate@{anchor data out}
       else certificate@{anchor data out})
    (@srefl@{top} Type@{out} T)
    (fun _ : T => unit -> T)
    cert_inhabitant@{anchor data out}.

Definition cert_payload@{anchor data out | anchor < data, data < out}
    : unit -> cert_choice@{anchor data out} :=
  fun _ => cert_inhabitant@{anchor data out}.

Definition cert_escaped@{lo lo' hi w z |
    lo = lo', lo < hi, hi < w, w < z}
    : cert_choice@{lo lo' hi}.
Proof.
  exact_no_check
    ((cert_payload@{lo hi w} : cert_force_type@{lo hi w z}) tt).
  Fail Defined. (* should fail *)
Abort.

(* Definition cert_collapse@{anchor data out | anchor < out, data < out} *)
(*     (x : cert_choice@{anchor data out}) : certificate@{anchor data out} := *)
(*   (match flag as b return *)
(*      (if b then certificate@{anchor data out} *)
(*       else certificate@{anchor data out}) -> certificate@{anchor data out} *)
(*    with *)
(*    | true => fun x => x *)
(*    | false => fun x => x *)
(*    end) x. *)

(* Definition cert_first@{anchor data out | anchor < out, data < out} *)
(*     (x : certificate@{anchor data out}) : Type@{data} := *)
(*   match x with existT _ A _ => A end. *)

(* Definition cert_second@{anchor data out | anchor < out, data < out} *)
(*     (x : certificate@{anchor data out}) *)
(*     : @eq Type@{out} (cert_first@{anchor data out} x) Type@{anchor} := *)
(*   match x as x return *)
(*     @eq Type@{out} (cert_first@{anchor data out} x) Type@{anchor} *)
(*   with existT _ A e => e end. *)

(* Definition cert_small@{lo lo' hi w z | *)
(*     lo = lo', lo < hi, hi < w, w < z} : Type@{lo} := *)
(*   cert_first@{lo lo' hi} *)
(*     (cert_collapse@{lo lo' hi} cert_escaped@{lo lo' hi w z}). *)

(* Definition cert_small_is_universe@{lo lo' hi w z | *)
(*     lo = lo', lo < hi, hi < w, w < z} *)
(*     : @eq Type@{hi} cert_small@{lo lo' hi w z} Type@{lo} := *)
(*   cert_second@{lo lo' hi} *)
(*     (cert_collapse@{lo lo' hi} cert_escaped@{lo lo' hi w z}). *)

(* Require Import Hurkens. *)

(* Definition contradiction : False := *)
(*   TypeNeqSmallType.paradox cert_small (eq_sym cert_small_is_universe). *)

(* Print Assumptions contradiction. *)
