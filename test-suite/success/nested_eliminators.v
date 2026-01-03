Notation "A -> B" := (forall (_ : A), B) (right associativity, at level 99).

Set Printing Universes.

Inductive nat : Type :=
| zero : nat
| S : nat -> nat.

Inductive bool : Type :=
| true : bool
| false : bool.

(* The type unit needs to be defined and registered to instantiate constant nesting. *)
Inductive unit : Set :=
    tt : unit.

Register unit as core.unit.type.
Register tt as core.unit.tt.


  (* Example with Template Inductive Types *)

Module Template.

  Set All Depth 2.

  Inductive True := c.

  (* Example with List *)
  Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.

  Arguments nil {_}.
  Arguments cons {_}.

  Inductive MRT : Set :=
  | MRTnode : list MRT -> MRT.

  Inductive RoseTree A : Type :=
  | RTleaf (a : A) : RoseTree A
  | RTnode (l : list (RoseTree A)) : RoseTree A.

  Inductive RoseRoseTree A : Type :=
  | Nleaf (a : A) : RoseRoseTree A
  | Nnode (p : (list (list (RoseRoseTree A)))) : RoseRoseTree A.

  Inductive ArrowTree1 A : Type :=
  | ATleaf1 (a : A) : ArrowTree1 A
  | ATnode1 (l : (bool -> list (ArrowTree1 A))) : ArrowTree1 A.

  Inductive ArrowTree2 A : Type :=
  | ATleaf2 (a : A) : ArrowTree2 A
  | ATnode2 (l : list (nat -> ArrowTree2 A)) : ArrowTree2 A.

  Inductive ArrowTree3 A : Type :=
  | ATleaf3 (a : A) : ArrowTree3 A
  | ATnode3 (l : (bool -> list (nat -> ArrowTree3 A))) : ArrowTree3 A.


  (* Example Prod *)
  Inductive prod (A B : Type) : Type :=
    pair : A -> B -> prod A B.

  Arguments pair {_ _}.

  Inductive PairTree A : Type :=
  | Pleaf (a : A) : PairTree A
  | Pnode (p : prod (PairTree A) (PairTree A)) : PairTree A.

  Inductive LeftTree A : Type :=
  | Lleaf (a : A) : LeftTree A
  | Lnode (p : prod (LeftTree A) nat) : LeftTree A.

  Scheme All for prod with true, false.

  Inductive LeftTree2 A : Type :=
  | Lleaf2 (a : A) : LeftTree2 A
  | Lnode2 (p : prod (LeftTree2 A) nat) : LeftTree2 A.

  Scheme All for prod with false, true.

  Inductive RightTree A : Type :=
  | Rleaf (a : A) : RightTree A
  | Rnode (p : prod nat (RightTree A)) : RightTree A.

  Inductive nu_nested (A B C : Type) : Type :=
  | nu_nested_nil : A -> nu_nested A B C
  | nu_nested_cons : list (nu_nested A (prod B B) C) -> nu_nested A B C.

  Inductive tricky1 A : Type :=
  | tricky11 : prod A nat -> tricky1 A.

  Inductive tricky2 A : Type :=
  | tricky21 : list A -> tricky2 A.

  Inductive tricky3 A : Type :=
  | tricky31 : prod A A -> tricky3 A
  | tricky32 : prod (list A) A -> tricky3 A.


  (* Nesting with vec *)
  Inductive vec A : nat -> Type :=
  | vnil : vec A zero
  | vcons : A -> forall n, vec A n -> vec A (S n).

  Inductive VecTree A : Type :=
  | VNleaf (a : A) : VecTree A
  | VNnode n (p : vec (VecTree A) n) : VecTree A.


  (* Example All2i *)
  Inductive All2i (A B : Type) (R : nat -> A -> B -> Type) (n : nat) : list A -> list B -> Type :=
    | All2i_nil : All2i A B R n nil nil
    | All2i_cons : forall (a : A) (b : B) (lA : list A) (lB : list B),
                  R n a b -> All2i A B R (S n) lA lB -> All2i A B R n (cons a lA) (cons b lB).

  (* Check specification given by the user is valid *)
  Fail Scheme All for All2i with true, false, true.

  Inductive typing A B (n : nat) (a : A) (b : B) : Type :=
  | typ_nil  : typing A B n a b
  | typ_cons : forall (lA : list A) (lB : list B),
              All2i A B (fun n => typing A B n) n lA lB -> typing A B n a b.


  (* Example All2i_bis_bis with trivial nesting on R *)
  Inductive All2i_bis (A B C : Type) (R : nat -> A -> B -> Type) (n : nat) : list A -> list B -> Type :=
    | All2i_bis_nil : C -> All2i_bis A B C R n nil nil
    | All2i_bis_cons : forall (a : A) (b : B) (lA : list A) (lB : list B),
                  R n a b -> All2i_bis A B C R (S n) lA lB -> All2i_bis A B C R n (cons a lA) (cons b lB).

  Inductive triv_All2_bis : Type :=
  | ctriv_All2_bis : All2i_bis bool bool triv_All2_bis (fun _ _ _ => nat) zero (@nil bool) (@nil bool) ->
                    triv_All2_bis.

  Scheme All for All2i_bis with false, false, true, false.

  Inductive triv_All2_bis2 : Type :=
  | ctriv_All2_bis2 : All2i_bis bool bool triv_All2_bis2 (fun _ _ _ => nat) zero (@nil bool) (@nil bool) ->
                    triv_All2_bis2.

End Template.



Module UnivPoly.

  (* Example with UnivPoly Inductive Types *)
  Set Universe Polymorphism.

  Set All Depth 2.


  (* Example with list *)
  Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.

  Inductive MRT : Set :=
  | MRTnode : list MRT -> MRT.

  Inductive RoseTree A : Type :=
  | RTleaf (a : A) : RoseTree A
  | RTnode (l : list (RoseTree A)) : RoseTree A.

  Inductive RoseRoseTree A : Type :=
  | Nleaf (a : A) : RoseRoseTree A
  | Nnode (p : (list (list (RoseRoseTree A)))) : RoseRoseTree A.

  Inductive ArrowTree3 A : Type :=
  | ATleaf3 (a : A) : ArrowTree3 A
  | ATnode3 (l : (bool -> list (nat -> ArrowTree3 A))) : ArrowTree3 A.


  (* Example with Prod *)
  Inductive prod (A B : Type) : Type :=
    pair : A -> B -> prod A B.

  Inductive PairTree A : Type :=
  | Pleaf (a : A) : PairTree A
  | Pnode (p : prod (PairTree A) (PairTree A)) : PairTree A.

  Inductive LeftTree A : Type :=
  | Lleaf (a : A) : LeftTree A
  | Lnode (p : prod (LeftTree A) nat) : LeftTree A.

  Inductive RightTree A : Type :=
  | Rleaf (a : A) : RightTree A
  | Rnode (p : prod nat (RightTree A)) : RightTree A.

End UnivPoly.



Module SortPoly.

  (* Example with a sort polymorphic containers *)
  Set Universe Polymorphism.

  Set All Depth 2.

  Inductive list@{sA;uA uR} (A : Type@{sA;uA}) : Type@{sA; uR} :=
  | nil : list A
  | cons : A -> list A -> list A.

  Inductive MRT : Set :=
  | MRTnode : list MRT -> MRT.

  Inductive SRT : SProp :=
  | SRTnode : list SRT -> SRT.

End SortPoly.



Module TestWarning.

  Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.

  Inductive MRT : Set :=
  | MRTnode : list MRT -> MRT.

End TestWarning.
