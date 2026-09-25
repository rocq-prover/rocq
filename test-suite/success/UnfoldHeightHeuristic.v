(* Test for the Kernel Unfold Height Heuristic flag. *)

(* Activate some debug messages to check computation of definitional height
   and that strategy levels are set for defined constants. *)
Set Debug "comDefinition".
Set Debug "vernacinterp".
Set Debug "defHeight".

(* Preliminary Sanity Checks*)

Set Kernel Conversion Height Heuristic.

(* Some dummy definitions to check (through log messages) that computed
   heights are correct, and that already computed heights are recovered
   from caché (field in const_body record) instead of re-computing.
*)
Definition c1 := 6.
Definition c2 := 8.

Definition c3 := if true then c1 else c2.
Definition c4 := if false then c3 else c2.
Definition c5 := if true then c1 else c3.

(* Check that strategy levels are correctly set.
   They should all be [-h] where [h] is the definitional height of the constant.
*)
Print Strategy c1.
Print Strategy c2.
Print Strategy c3.
Print Strategy c4.
Print Strategy c5.


(* Tests for the Heuristic *)

(* Disable the flag before definitions are declared.
   Otherwise, strategy levels are going to be set and, even if we
   unset the flag before we run the tests, the conversion will still
   be guided by those strategy levels. *)

Unset Kernel Conversion Height Heuristic.

Fixpoint fact (n : nat) :=
match n with
| O => 1
| S k => n * fact k
end.

(* [fact200'] depends on [fact200], so the definitional height of the former
   is greater than that of the latter.
   However, since the flag is unset, they are not computed and no strategy
   level is registered for these constants. *)
Definition fact200 := fact 200.
Definition fact200' := fact200.

(* We can see that both are [transparent]. *)
Print Strategy fact200.
Print Strategy fact200'.


(* Case 1a: This is fast because the right side is unfolded first by default
   when both constants have the same strategy. So the equality is found
   in one step. *)
Timeout 1 Check eq_refl : fact200 = fact200'.

(* Case 1b: This times out because [fact200] is unfolded and reduced first,
   and so a costly computation is performed before [fact200'] is unfolded
   even once. *)
Fail Timeout 1 Check eq_refl : fact200' = fact200.


(* With the Heuristic.
   Strategy levels are assigned according to definitional heights when
   constants are declared, with higher constants having a higher priority
   for unfolding during conversion.
*)
Set Kernel Conversion Height Heuristic.

Definition new_fact200 := fact 200.
Definition new_fact200' := new_fact200.

(* [new_fact200'] depends on [new_fact200] and this is reflected
   by the assigned strategy levels.
*)
Print Strategy new_fact200.
Print Strategy new_fact200'.

(* Case 2a: This is still fast. *)
Timeout 1 Check eq_refl : new_fact200 = new_fact200'.
(* Case 2b: Even though [new_fact200'] appears on the left, conversion
   unfolds it first guided by its strategy level. *)
Timeout 1 Check eq_refl : new_fact200' = new_fact200.


(* Additional Sanity Checks
   Interactive definitions also profit from the heuristic.
   When they are ended transparently (w/ [Defined.] or [Defined ident.],
   the height is computed and a strategy level is assigned.)
*)

(* Make sure that setting strategy levels is not attempted for
   failed interactive definitions. *)
Lemma bogus : 1 = 2.
Proof.
    exact_no_check (eq_refl 1).
Fail Qed.
Abort.


Definition three : nat.
Proof. exact 3. Defined.

Print Strategy three.


#[refine]
Definition plus_2_4 : nat := _ + _.
Proof. exact 2. exact 4. Defined plus_2_4.

Print Strategy plus_2_4.

(* Opaque definitions are not considered by the heuristic. *)
Goal forall n, n + 0 = n.
Proof.
induction n; auto.
Save add_n_0.
