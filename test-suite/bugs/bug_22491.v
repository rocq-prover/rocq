(* [with Module M := F] where the field being pinned is a functor.

   The objects of the replacement used to be built with an empty parameter
   list, [expand_sobjs] having dropped the parameters of [F]. The object layer
   then took the field for a plain module: it pushed names for the fields of
   [F]'s body at paths where the kernel has a functor and no field at all, so
   that using one was an anomaly,

     Anomaly "Constant Impl.M.a does not appear in the environment."

   while applying the field, which is what one declared it for, was rejected
   with "Application of a functor with too few arguments". *)

Module Type T. Parameter a : bool. End T.
Module GM. Definition a := true. End GM.
Module F (X : T). Definition a := X.a. End F.
Module Type FT. Declare Module M (X : T) : T. End FT.
Module Type FT2 := FT with Module M := F.

Module Impl : FT2. Module M := F. End Impl.

(* The fields of a functor are not names of their own. *)
Fail Check Impl.M.a.

(* Applying it is, and it computes. *)
Module R := Impl.M GM.
Definition v : R.a = true := eq_refl.

(* Same through an abstract implementation, ... *)
Declare Module Abs : FT2.
Module RA := Abs.M GM.

(* ... and through a functor over the refined signature. *)
Module Z (W : FT2). Module RW := W.M GM. Definition c := RW.a. End Z.
Module ZI := Z Impl.
Definition vz : ZI.c = true := eq_refl.

(* The pin itself is enforced: an implementation must agree with [F]. *)
Module G (X : T). Definition a := negb X.a. End G.
Module BadImpl. Module M := G. End BadImpl.
Fail Module Bad : FT2 := BadImpl.
