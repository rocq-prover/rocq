Set Universe Polymorphism.

Record TYPE@{i} := cType {
  type : Type@{i};
}.

Definition PROD@{i j k}
  (A : Type@{i})
  (B : A -> Type@{j})
  : TYPE@{k}.
Proof.
  refine (cType@{i} _).
+ refine (forall x : A, B x).
Defined.

Local Unset Strict Universe Declaration.
Definition PRODinj
  (A : Type@{i})
  (B : A -> Type@{_})
  : TYPE.
Proof.
  refine (cType@{i} _).
+ refine (forall x : A, B x).
Defined.

  Monomorphic Universe i j.
  Monomorphic Constraint j < i.
Set Printing Universes.
Check PROD@{i i i}.
(* The universe of [B] is raised to [i], its upper bound: [PRODinj@{i}] *)
Check fun (A : Type@{i}) (B : A -> Type@{j}) => PRODinj@{i} A B.
Fail Check fun (A : Type@{j}) (B : A -> Type@{i}) => PRODinj@{j} A B.
