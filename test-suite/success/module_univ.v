(* Universe parameters of module types and universe definitions of modules *)

Module Type Foo.
  Universe Parameter u.
  Fail Universe Parameter u.

  Parameter type : Type@{u}.

  Parameter empty : type.
End Foo.

Module AFoo : Foo.
  Universe Definition u := Set.
  Definition type : Set := list nat.
  Definition empty : type := nil.
End AFoo.
Print Universes Subgraph (AFoo.u).
Definition idS (A : Set) (a : A) := a.
Print Universes.
Check idS AFoo.type.
Check (AFoo.type : Type@{AFoo.u}).
Check (AFoo.empty : AFoo.type).

(* With a transparent ascription, the definition of the universe is visible *)
Module BFoo <: Foo.
  Universe Definition u := Set.
  Definition type : Set := bool.
  Definition empty : type := true.
End BFoo.

Check (BFoo.type : Set).
Check (BFoo.type : Type@{BFoo.u}).

Universe big.
Constraint Set < big.

Module BFooBig <: Foo.
  Universe Definition u := big.
  Definition type : Type@{u} := Set.
  Definition empty : type := unit.
End BFooBig.

Fail Check (BFooBig.type : Set).
Check (BFooBig.type : Type@{BFooBig.u}).

(* Functors instantiate the universe parameter at each application *)
Module F (X : Foo).
  Definition t : Type@{X.u} := X.type.
  Definition l : Type@{X.u} := list X.type.
End F.

Module FA := F AFoo.
Set Printing Universes.
Check (FA.t : Type@{AFoo.u}).
Module FB := F BFoo.
Check (FB.l : Set).

(* Aliases get a universe equal to the one of the aliased module *)
Module CFoo := AFoo.
Check (AFoo.type : Type@{CFoo.u}).
Check (CFoo.type : Type@{AFoo.u}).

(* Inclusion copies the universe *)
Module DFoo.
  Include AFoo.
End DFoo.
Check (DFoo.type : Type@{DFoo.u}).
Check (DFoo.type : Type@{AFoo.u}).

(* Universe parameters may be constrained by the body of the module type *)
Universe v.
Module Type Big.
  Universe Parameter u.
  Lemma t : Type@{v}. Proof. exact Type@{u}. Qed.
End Big.

Module ABig : Big.
  Universe w.
  Constraint w < v.
  Universe Definition u := w.
  Definition t : Type@{v} := Type@{u}.
End ABig.

Module G (X : Big).
  Definition t := X.t.
End G.

Module GA := G ABig.

(* The constraints of the signature are checked at functor application *)
Module BBig.
  Universe Definition u := v.
  Definition t : Type@{v} := nat.
End BBig.

Fail Module GB := G BBig.

(* As for constants, a universe definition of the signature can only be
   implemented by a universe definition *)
Module Type FooDef.
  Universe Definition u := Set.
  Parameter t : Type@{u}.
End FooDef.
Module G2 (X : FooDef). Definition t : Set := X.t. End G2.

Module Good.
  Universe Definition u := Set.
  Definition t : Type@{u} := nat.
End Good.
Module G2G := G2 Good.

Module Bad.
  Universe Parameter u.
  Definition t : Type@{u} := nat.
End Bad.
Fail Module G2B := G2 Bad.


Module Bad2.
  Universe Definition u := big.
  Definition t : Type@{u} := nat.
End Bad2.
Fail Module G2B := G2 Bad2.

(* Universe parameters of modules *)
Module Param.
  Universe Parameter u.
  Definition t := Type@{u}.
End Param.

Check (Param.t : Type@{Param.u+1}).

(* Higher-order functors: the universes of the functor parameters are
   declared for the subtyping check *)
Module Type FT (X : Foo).
  Parameter s : Type@{X.u}.
End FT.
Module FS (X : Foo).
  Definition s : Set := nat.
End FS.
Module H (Y : FT). End H.
Module HF := H FS.
Module FS' : FT := FS.

(* Printing *)
Print Module Type Foo.
Print Module AFoo.
Print Module BFoo.

Module Type T.
  Universe Parameter u.
  Parameter t : Type@{u}.
End T.

(* Polymorphic maps with precise universes *)
Set Universe Polymorphism.
Module Type Map (X: T).
  Polymorphic Parameter t@{i} : Type@{i} -> Type@{max(i,X.u)}.

  (* Requires X.u <= i just to simplify the instance in ListMap.
    With algebraics in instances we will be able to instantiate list_map@{max(i,Xu) max(i,Xu)}
    without a proxy universe, avoiding this constraint *)
  Parameter map@{i | X.u <= i} : forall (A B : Type@{i}), (A -> B) -> t A -> t B.
End Map.
From Corelib Require Import ListDef.

Fixpoint list_map {A B : Type} (f : A -> B) (l : list A) : list B :=
  match l with
  | nil => nil
  | cons x xs => cons (f x) (list_map f xs)
  end.
Module ListMap (X : T).
  Definition t@{i} (A : Type@{i}) : Type@{max(i,X.u)} := list (X.t * A).
  Definition map@{i | X.u <= i} (A B : Type@{i}) (f : A -> B) (x : t A) := list_map@{i i} (fun '(k, x) => (k, f x)) x.
End ListMap.

Module ListMap' : Map := ListMap.

Module SmallFunctor (X : T).
  (* This forces a constraint on the input universes, preventing some instantiations *)
  Monomorphic Constraint X.u = Set.
End SmallFunctor.

Module XNat <: T.
  Universe Definition u := Set.
  Monomorphic Definition t := nat.
End XNat.
Module NatListMap := ListMap XNat.
Module NatSmall := SmallFunctor XNat.

Module XBig <: T.
  Universe Definition u := big.
  Monomorphic Definition t := Set.
End XBig.
Print Module XBig.
Module BigListMap := ListMap XBig.
Fail Module BigSmall := SmallFunctor XBig.

Print Module XNat.
Print Universes Subgraph (XNat.u).
Print Module NatListMap.

Check NatListMap.map@{Set} nat nat (fun x => x) : list (nat * nat) -> list (nat * nat).
Unset Universe Polymorphism.

(* Check that functor application is more stringent than ascription *)

Module Type CstrsLoose.
  Universe Parameter u.
  Universe Parameter v.
  Parameter t : Type@{u}.
End CstrsLoose.

Module CBad : CstrsLoose.
  Universe Definition u := big.
  Universe Definition v := Set.
  Definition t : Type@{u} := nat.
End CBad.

Module CGood : CstrsLoose.
  Universe Definition u := Set.
  Universe Definition v := big.
  Definition t : Type@{u} := nat.
End CGood.

Module Fn (X : CstrsLoose).
  Constraint X.u < X.v.
End Fn.

(** Cannot apply as CBad has u < v *)
Fail Module FooBad := Fn CBad.
Module FooGood := Fn CGood.

Print Module FooGood.

(* Check that constraints on parameter universes hold for each instance *)
Module Type Cstrs.
  Universe Parameter u.
  Universe Parameter v.
  Constraint u < v.
End Cstrs.

Universe bigger.
Constraint big < bigger.
(*
Module C' : Cstrs.
  Universe Definition u := big.
  Universe Definition v := Set.
  Fail End C'.
  Reset v.
  Universe Definition v := bigger.
End C'.
*)

(* The universes of the parameters of an algebraic functor are not in the
   global universe graph: the subtyping checks of the body must declare them
   (anomaly "Universe M.u undefined" otherwise) *)
Universe i.
Module Type E'. Parameter t : Set. End E'.
Module Type WSfun (X : E').
  Universe Parameter u.
  Parameter t : Type@{u}.
  (* A constraint of the signature on its universe parameter: u <= i *)
  Definition tt : Type@{i} := t.
End WSfun.
Module Type WS. Declare Module X : E'. Include WSfun X. End WS.
Module WFacts_fun (Import X : E') (Import M : WSfun X).
  Definition foo : Type@{M.u} := M.t.
End WFacts_fun.
Module WFacts (M : WS) := WFacts_fun M.X M.
Module Facts := WFacts.

(* The constraints that the subtyping checks of a functor infer on the
   universes of its parameters or components cannot be added globally: for
   an interactive functor, they are checked while the functor is open and
   become constraints of the functor, checked at each application; for a
   functor declared as a whole, they must be declared in its module type *)
Universe n.
Module Type TN. Universe Parameter u. Parameter t : Type@{u}. End TN.
Module Type FTN. Parameter t : Type@{n}. End FTN.
Module GN (X : TN). Definition t := X.t. End GN.
Fail Module FN (X : TN) : FTN := GN X.
Fail Module FN (X : TN) <: FTN := GN X.
Module FN (X : TN) <: FTN.
  (* Universe Definition u := X.u. *)
  Definition t := X.t. (* requires X.u <= n *)
End FN.
Module AN.
  Universe Definition u := n.
  Definition t : Type@{u} := nat.
End AN.
Module FNA := FN AN.
Check (FNA.t : Type@{n}).
Universe bign.
Constraint n < bign.
Module BN.
  Universe Definition u := bign.
  Definition t : Type@{u} := Type@{n}.
End BN.
Fail Module FNB := FN BN.

(* [with Universe Definition u := v] defines a universe parameter of a module
   type; [with Definition c := t] is only allowed if the type of c does not
   depend on a universe parameter that is still abstract *)
Universe iw.
Module Type TW. Universe Parameter ut. Parameter t : Type@{ut}. End TW.
Fail Module Type TI := TW with Definition t := Type@{iw}.
Universe jw.
Constraint iw < jw.
Module Type TI := TW with Universe Definition ut := jw with Definition t := Type@{iw}.
Print Module Type TI.
(* iw < iw *)
Fail Module Type TI' := TW with Universe Definition ut := iw with Definition t := Type@{iw}.
(* ut is already defined *)
Fail Module Type TI' := TI with Universe Definition ut := jw.
(* t is not a universe *)
Fail Module Type TI' := TW with Universe Definition t := jw.
(* Also in submodules *)
Module Type TWS. Declare Module X : TW. Parameter s : X.t. End TWS.
Fail Module Type TIS := TWS with Definition X.t := nat.
Module Type TIS := TWS with Universe Definition X.ut := Set with Definition X.t := nat.
Module MIS : TIS. Module X. Universe Definition ut := Set. Definition t := nat. End X. Definition s := 0. End MIS.
Module FI (M : TI).
  (* M.ut = jw *)
  Definition x : Type@{M.ut} := Type@{iw}.
End FI.
Module MI : TI. Universe Definition ut := jw. Definition t := Type@{iw}. End MI.
Module FMI := FI MI.
Module MI' : TI.
  Universe Definition ut := iw.
  Definition t := Type@{iw}.
  Fail End MI'.
  Reset ut.
  Universe Definition ut := jw.
  Definition t := Type@{iw}.
End MI'.
