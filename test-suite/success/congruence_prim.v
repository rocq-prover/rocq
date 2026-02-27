Require Import Corelib.Numbers.Cyclic.Int63.PrimInt63.
Require Import Corelib.Strings.PrimString.
Require Import Corelib.Floats.PrimFloat.
Require Import Corelib.Array.PrimArray.

Inductive Box (A : Type) := box : A -> Box A.

Arguments box {A}.

Goal box 0%uint63 = box 1%uint63 -> False.
Proof.
congruence.
Abort.

Goal box "true"%pstring = box "false"%pstring -> False.
Proof.
congruence.
Qed.

Goal box 1.0%float = box 2.0%float -> False.
Proof.
congruence.
Qed.

(* Arrays *)

(* TODO: array length *)
Goal forall x : bool, [| x | x |] = [| | x |] -> False.
Proof.
  Fail congruence.
Abort.

(* (dis)equality in the array contents *)
Goal forall x y:bool, x = y -> [| x | x|] = [| y |x|].
Proof.
  intros.
  congruence.
Qed.
Goal forall x y:bool, [| x | x|] = [| y |x|] -> x = y.
Proof.
  intros.
  congruence.
Qed.
Goal forall x y:bool, [| true | x|] = [| false |x|] -> False.
Proof.
  intros.
  congruence.
Qed.

(* same tests with more items to test index computations *)
Goal forall x y t:bool, x = y -> [| t; x; t | x|] = [| t; y; t |x|].
Proof.
  intros.
  congruence.
Qed.
Goal forall x y t:bool, [| t; true; t | x|] = [| t; false; t |x|] -> False.
Proof.
  intros.
  congruence.
Qed.

Goal forall x y t:bool, x = y -> [| x; t; x | x|] = [| y; t; y |x|].
Proof.
  intros.
  congruence.
Qed.
Goal forall x y t:bool, [| true; t; true | x|] = [| false; t; true |x|] -> False.
Proof.
  intros.
  congruence.
Qed.
Goal forall x y t:bool, [| true; t; true | x|] = [| true; t; false |x|] -> False.
Proof.
  intros.
  congruence.
Qed.

(* equality in the default element *)
Goal forall x y t:bool, x = y -> [| | x|] = [| | y|].
Proof.
  intros.
  congruence.
Qed.
Goal forall x y t:bool, [| | true|] = [| | false|] -> False.
Proof.
  intros.
  congruence.
Qed.


(* equality in both default element and contents *)
Goal forall x y a b:bool, a = b -> x = y -> [|a | x|] = [|b | y|].
Proof.
  intros.
  congruence.
Qed.

(* equality in the type; not expected to make progress but must not raise anomalies *)
Goal forall x y t:bool, bool = bool -> [|t | x|] = [|t | y|].
Proof.
  intros.
  Fail congruence.
Abort.

(* TODO: Performance test for big arrays. *)
Goal forall x y : bool, make 12 x = make 12 y -> x = y.
Proof.
  lazy.
  intros.
  Timeout 1 congruence.
Abort.
