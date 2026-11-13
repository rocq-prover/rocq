(* Labels that coqc lets repeat. A constant and a module of one structure
   share a label, since they are in two namespaces, and so do fields of two
   structures. An Include adds the fields of another structure, a with
   constraint replaces a field of a module type, and a functor application
   copies the fields of the functor's body. *)

Unset Elimination Schemes.

Inductive unit : Set := tt.

(* The label M for a constant and for a module of the library, and again
   in the module's own structure. *)
Definition M : unit := tt.

Module M.
  Definition M : unit := tt.
  Module M.
    Definition M : unit := tt.
  End M.
End M.

Module Type T.
  Parameter t : Set.
  Parameter x : t.
End T.

Definition T : unit := tt.

Module Type U := T with Definition t := unit.

Module A : U.
  Definition t := unit.
  Definition x := tt.
End A.

(* The functor's body includes the fields of its parameter. *)
Module F (X : T).
  Include X.
  Definition y : t := x.
End F.

Module B := F A.

Module C.
  Include F A.
  Definition z : t := y.
End C.

(* A block of two types and three constructors. *)
Inductive Even : Prop := even_odd : forall _ : Odd, Even
with Odd : Prop := odd_even : forall _ : Even, Odd | odd_tt : Odd.
