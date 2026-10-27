(* Library for univ_template.v: a functor declaring a template polymorphic
   inductive type whose sort mentions a universe of a functor parameter *)
Module Type OT. Universe Parameter ut. Parameter t : Type@{ut}. End OT.
Module Raw (X : OT).
  Definition t (elt : Type) := list (X.t * elt).
End Raw.
Module Make (X : OT).
  Module Raw := Raw X.
  Record slist (elt : Type) := { this :> Raw.t elt }.
  Definition t (elt : Type) : Type := slist elt.
End Make.
Module Make_ord (X D : OT).
  Module MapS := Make X.
  Import MapS.
  (* The sort of slist must mention the universe of this functor's X, not of
     Make's: the constraints of this definition become constraints of Make_ord *)
  Definition eq (m m' : t D.t) := this _ m = this _ m'.
End Make_ord.

(* Module types for the [with Definition] tests of univ_template.v *)
Module Type Typ. Universe Parameter ut. Parameter t : Type@{ut}. End Typ.
Module Type WS. Declare Module E : Typ. Parameter s : E.t. End WS.

(* A universe definition equal to a global universe of this library: the
   checker must declare the universes of an admitted library before adding
   its components (rocqchk -o -norec) *)
Universe ulib.
Module NL. Universe Definition ut := ulib. Definition t : Type@{ut} := nat. End NL.
