(* -*- coqchk-prog-args: ("-o") -*- *)
(* The sorts of a template polymorphic inductive type are substituted through
   functor application: otherwise the universes of the parameters of the
   functor leak into the constraints of the enclosing functor, and applying
   it from another file fails with "Universe X.ut undefined" *)
Require Import univ_template_lib.
Module N. Universe Definition ut := Set. Definition t : Type@{ut} := nat. End N.
Module LO := Make_ord N N.
Check (LO.eq : LO.MapS.t N.t -> LO.MapS.t N.t -> Prop).

(* [with Universe Definition] and [with Definition] on components of a module
   type required from another file: its universes are not part of the global
   graph *)
Module OT <: Typ with Universe Definition ut := Set with Definition t := nat.
  Universe Definition ut := Set.
  Definition t := nat.
End OT.
Fail Module F (E : Typ) (M : WS with Definition E.t := E.t).
Module F (E : Typ) (M : WS with Universe Definition E.ut := E.ut with Definition E.t := E.t).
  (* M.E.ut = E.ut *)
  Definition s : Type@{M.E.ut} := E.t.
End F.
Module G (E : Typ) (M : WS with Module E := E). Definition s := M.s. End G.
Universe big.
Constraint Set < big.
(* The same type as OT.t, in a bigger universe *)
Module Big. Universe Definition ut := big. Definition t : Type@{ut} := nat. End Big.
Module WSmall. Module E := OT. Definition s : E.t := 0. End WSmall.
Module WBig. Module E := Big. Definition s : E.t := 0. End WBig.
Module FOK := F OT WSmall.
Module FOK2 := F Big WBig.
(* WSmall.E.ut = Set is not Big.ut *)
Fail Module FBad := F Big WSmall.
