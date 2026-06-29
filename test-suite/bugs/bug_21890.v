(* -*- mode: coq; coq-prog-args: () -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 53 lines to 54 lines, then from 68 lines to 2005 lines, then from 2007 lines to 73 lines, then from 87 lines to 247 lines, then from 254 lines to 102 lines, then from 116 lines to 528 lines, then from 531 lines to 103 lines, then from 118 lines to 105 lines, then from 120 lines to 87 lines, then from 102 lines to 87 lines, then from 0 lines to 87 lines *)
(* coqc version 9.2+rc2 compiled with OCaml 4.14.2
   coqtop version 9.2+rc2
   Expected coqc runtime on this file: 0.000 sec
   Expected coqc peak memory usage on this file: 0.0 kb *)

Global Set Definitional UIP.
Module Export IsomorphismDefinitions.
#[export]
Set Universe Polymorphism.
Inductive eq@{s|u|} {α:Type@{s|u}} (a:α) : α -> SProp
  := eq_refl : eq a a.

#[local] Notation "x = y" := (eq x y) : type_scope.
#[export]
Set Implicit Arguments.

Record Iso@{s s'|u u'|} (A : Type@{s|u}) (B : Type@{s'|u'}) := {
    to :> A -> B;
    from : B -> A;
    to_from : forall x, to (from x) = x;
    from_to : forall x, from (to x) = x;
}.
#[local] Set Primitive Projections.
Record > rel_iso@{s s'|u u'|} {A B} (i : Iso@{s s'|u u'} A B) (x : A) (y : B) : SProp := { proj_rel_iso :> i.(to) x = y }.

Existing Class Iso.

End IsomorphismDefinitions.

Variant SInhabited (A : Prop) : SProp := sinhabits : A -> SInhabited A.
Axiom sinhabitant@{} : forall {A : Prop}, SInhabited A -> A.

Module Import IsoEq.
#[local] Notation "x = y" := (IsomorphismDefinitions.eq x y) : type_scope.
Theorem f_equal@{s s'|u u'|} {A : Type@{s|u}} {B : Type@{s'|u'}} (f : A -> B) {x y : A} (H : x = y) : f x = f y.
Admitted.
Lemma seq_of_peq_t@{u} {A : Prop} {x y : A} (H : Logic.eq x y) : IsomorphismDefinitions.eq@{Type|u} x y.
Admitted.

End IsoEq.
Module Export Imported.
#[local] Unset Implicit Arguments.
Inductive Eq@{s|u|} (A : Type@{s|u}) (a : A) : A -> SProp :=
| Eq_refl : Eq A a a.
End Imported.
Axiom proof_irrelevance : forall P : Prop, forall p1 p2 : P, p1 = p2.
Monomorphic Definition imported_Corelib__Init__Logic__eq : forall x : Type, x -> x -> SProp.
exact ((@Imported.Eq)).
Defined.
Monomorphic Instance Corelib__Init__Logic__eq_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib__Init__Logic__eq x4 x6).
Proof.
  intros x1 x2 hx x3 x4 [H1] x5 x6 [H2].
  destruct H1.
destruct H2.
  unshelve refine {| to := _; from := _; to_from := _; from_to := _ |}.
  -
 intro H.
destruct H.
exact (Imported.Eq_refl _ _).
  -
 intro H.
apply sinhabitant.
    refine (match H in Imported.Eq _ _ z return
              forall y, IsomorphismDefinitions.eq (hx.(to) y) z -> SInhabited (x3 = y) with
            | Imported.Eq_refl _ _ => _ end x5 _).
    +
 intros y Hy.
      pose proof (f_equal hx.(from) Hy) as Hy2.
      pose proof (hx.(from_to) x3) as E1.
      pose proof (hx.(from_to) y) as E2.
      constructor.
      revert E1 E2 Hy2.
generalize (hx.(from) (hx.(to) x3)) (hx.(from) (hx.(to) y)).
      intros a b Ea Eb Eab.
destruct Ea.
destruct Eb.
destruct Eab.
reflexivity.
    +
 reflexivity.
  -
 cbv beta.
intro x.
reflexivity.
  -
 cbv beta.
intro x.
exact (IsoEq.seq_of_peq_t (@proof_irrelevance _ _ _)).
Abort.
(* File "./bug_not_found_02.v", line 91, characters 7-51:
Error: Anomaly "Uncaught exception Not_found."
Please report at http://rocq-prover.org/bugs/.
Raised at Environ.lookup_rel in file "kernel/environ.ml", line 143, characters 29-44
Called from Evarsolve.invert_definition.imitate in file "pretyping/evarsolve.ml", line 1720, characters 15-40
Called from CArray.Smart.map in file "clib/cArray.ml", line 455, characters 15-18
Called from Constr.map_invert in file "kernel/constr.ml", line 633, characters 19-44
Called from Termops.map_constr_with_full_binders in file "engine/termops.ml", line 661, characters 16-35
Called from Termops.map_constr_with_full_binders in file "engine/termops.ml", line 644, characters 15-20
Called from Termops.map_constr_with_full_binders in file "engine/termops.ml", line 636, characters 15-53
Called from Termops.map_constr_with_full_binders in file "engine/termops.ml", line 636, characters 15-53
Called from Termops.map_constr_with_full_binders.f_ctx in file "engine/termops.ml", line 656, characters 17-46
Called from Stdlib__Array.map2 in file "array.ml", line 120, characters 24-61
Called from Termops.map_constr_with_full_binders in file "engine/termops.ml", line 663, characters 16-39
Called from Termops.map_constr_with_full_binders in file "engine/termops.ml", line 644, characters 15-20
Called from Stdlib__Array.map in file "array.ml", line 108, characters 21-40
Called from Termops.map_constr_with_full_binders in file "engine/termops.ml", line 645, characters 16-34
Called from Termops.map_constr_with_full_binders in file "engine/termops.ml", line 636, characters 15-53
Called from Termops.map_constr_with_full_binders in file "engine/termops.ml", line 636, characters 15-53
Called from Termops.map_constr_with_full_binders.f_ctx in file "engine/termops.ml", line 656, characters 17-46
Called from Stdlib__Array.map2 in file "array.ml", line 120, characters 24-61
Called from Termops.map_constr_with_full_binders in file "engine/termops.ml", line 663, characters 16-39
Called from Termops.map_constr_with_full_binders in file "engine/termops.ml", line 644, characters 15-20
Called from Stdlib__Array.map in file "array.ml", line 108, characters 21-40
Called from Termops.map_constr_with_full_binders in file "engine/termops.ml", line 645, characters 16-34
Called from Evarsolve.invert_definition in file "pretyping/evarsolve.ml", line 1825, characters 11-31
Called from Evarsolve.evar_define.(fun) in file "pretyping/evarsolve.ml", line 1850, characters 22-91
Called from Evarsolve.solve_simple_eqn in file "pretyping/evarsolve.ml", line 1926, characters 14-79
Called from Evarconv.evar_conv_x in file "pretyping/evarconv.ml", line 729, characters 19-124
Called from Evarconv.ise_app_rev_stack2 in file "pretyping/evarconv.ml", line 437, characters 29-48
Called from Evarconv.ise_app_rev_stack2 in file "pretyping/evarconv.ml", line 435, characters 13-55
Called from Evarconv.exact_ise_stack2.ise_rev_stack2 in file "pretyping/evarconv.ml", line 607, characters 21-61
Called from Evarconv.evar_conv_x.default in file "pretyping/evarconv.ml", line 717, characters 10-120
Called from Evarconv.evar_conv_x in file "pretyping/evarconv.ml", line 1498, characters 4-46
Called from Evarconv.unify_leq_delay in file "pretyping/evarconv.ml", line 2121, characters 8-45
Called from Coercion.inh_conv_coerce_to_fail in file "pretyping/coercion.ml", line 723, characters 7-44
Called from Coercion.inh_conv_coerce_to_gen in file "pretyping/coercion.ml", line 762, characters 33-126
Called from Coercion.inh_conv_coerce_to_gen in file "pretyping/coercion.ml", line 792, characters 6-106
Re-raised at Exninfo.iraise in file "clib/exninfo.ml", line 81, characters 4-38
Called from Pretyping.Default.pretype_app in file "pretyping/pretyping.ml", line 1196, characters 30-87
Called from Pretyping.pretype in file "pretyping/pretyping.ml" (inlined), line 1681, characters 2-57
Called from Pretyping.ise_pretype_gen in file "pretyping/pretyping.ml", line 1704, characters 21-79
Called from Pretyping.understand_ltac in file "pretyping/pretyping.ml" (inlined), line 1764, characters 22-65
Called from Pretyping.understand_uconstr in file "pretyping/pretyping.ml", line 1781, characters 2-57
Called from Ltac_plugin__Internals.exact.(fun) in file "plugins/ltac/internals.ml", line 197, characters 17-70
Called from Proofview.Goal.enter.f in file "engine/proofview.ml", line 1177, characters 40-46
Re-raised at Exninfo.iraise in file "clib/exninfo.ml", line 81, characters 4-38
Called from Proof.run_tactic in file "proofs/proof.ml", line 321, characters 4-49
Called from Proof.solve in file "proofs/proof.ml", line 447, characters 39-60
Called from ComTactic.solve_core.(fun) in file "vernac/comTactic.ml", line 76, characters 23-75
Called from Declare.Proof.map_fold_endline in file "vernac/declare.ml", line 1803, characters 20-48
Called from ComTactic.solve_core in file "vernac/comTactic.ml", line 73, characters 23-459
Called from Vernactypes.vtmodifyproof.(fun) in file "vernac/vernactypes.ml", line 185, characters 32-47
Called from Vernactypes.typed_vernac.(fun) in file "vernac/vernactypes.ml", line 170, characters 65-71
Called from Vernactypes.run.(fun) in file "vernac/vernactypes.ml", line 164, characters 15-32
Called from Vernactypes.combine_runners.(fun) in file "vernac/vernactypes.ml", line 126, characters 16-23
Called from Vernactypes.OpaqueAccess.runner.(fun) in file "vernac/vernactypes.ml", line 114, characters 30-34
Called from Vernactypes.combine_runners.(fun) in file "vernac/vernactypes.ml", line 125, characters 14-100
Called from Vernactypes.combine_runners.(fun) in file "vernac/vernactypes.ml", line 126, characters 16-23
Called from Vernactypes.Proof.runner.(fun) in file "vernac/vernactypes.ml", line 72, characters 19-22
Called from Vernactypes.combine_runners.(fun) in file "vernac/vernactypes.ml", line 125, characters 14-100
Called from Vernactypes.Prog.runner.(fun) in file "vernac/vernactypes.ml", line 27, characters 30-34
Called from Vernactypes.combine_runners.(fun) in file "vernac/vernactypes.ml", line 124, characters 12-173
Called from Vernactypes.combine_runners.(fun) in file "vernac/vernactypes.ml", line 124, characters 12-173
Called from Vernactypes.run in file "vernac/vernactypes.ml", line 163, characters 14-96
Called from Vernacinterp.interp_expr_core in file "vernac/vernacinterp.ml", line 80, characters 60-157
Called from Vernacinterp.interp_expr in file "vernac/vernacinterp.ml", line 49, characters 19-121
Called from Stdlib__Fun.protect in file "fun.ml", line 33, characters 8-15
Re-raised at Stdlib__Fun.protect in file "fun.ml", line 38, characters 6-52
Called from VernacControl.under_control in file "vernac/vernacControl.ml", line 211, characters 14-18
Called from Vernacinterp.interp_control_gen in file "vernac/vernacinterp.ml", line 36, characters 4-208
Called from Stdlib__Fun.protect in file "fun.ml", line 33, characters 8-15
Re-raised at Stdlib__Fun.protect in file "fun.ml", line 38, characters 6-52
Called from Stdlib__Fun.protect in file "fun.ml", line 33, characters 8-15
Re-raised at Stdlib__Fun.protect in file "fun.ml", line 38, characters 6-52
Called from Vernacinterp.interp_gen in file "vernac/vernacinterp.ml", line 151, characters 16-41
Re-raised at Exninfo.iraise in file "clib/exninfo.ml", line 81, characters 4-38
Called from Vernacinterp.interp in file "vernac/vernacinterp.ml", line 165, characters 15-115
Called from Stm.Reach.known_state.reach.(fun) in file "stm/stm.ml", line 2026, characters 20-47
Called from Stm.Reach.known_state.resilient_tactic in file "stm/stm.ml", line 1965, characters 10-14
Re-raised at Exninfo.iraise in file "clib/exninfo.ml", line 81, characters 4-38
Called from Stm.State.define in file "stm/stm.ml", line 963, characters 6-10
Re-raised at Exninfo.iraise in file "clib/exninfo.ml", line 81, characters 4-38
Called from Stm.Reach.known_state.reach in file "stm/stm.ml", line 2204, characters 4-105
Called from Stm.observe in file "stm/stm.ml", line 2296, characters 4-60
Re-raised at Exninfo.iraise in file "clib/exninfo.ml", line 81, characters 4-38
Called from Vernac.interp_vernac in file "toplevel/vernac.ml", line 83, characters 29-50
Re-raised at Exninfo.iraise in file "clib/exninfo.ml", line 81, characters 4-38
Called from Stdlib__Fun.protect in file "fun.ml", line 33, characters 8-15
Re-raised at Stdlib__Fun.protect in file "fun.ml", line 38, characters 6-52
Called from Stdlib__Fun.protect in file "fun.ml", line 33, characters 8-15
Re-raised at Stdlib__Fun.protect in file "fun.ml", line 38, characters 6-52
Called from Vernac.load_vernac_core.loop in file "toplevel/vernac.ml", line 127, characters 8-774
Called from Vernac.load_vernac_core in file "toplevel/vernac.ml", line 150, characters 6-19
Re-raised at Exninfo.iraise in file "clib/exninfo.ml", line 81, characters 4-38
Called from Vernac.load_vernac in file "toplevel/vernac.ml", line 227, characters 30-83
Called from Ccompile.compile in file "toplevel/ccompile.ml", line 62, characters 18-78
Called from Ccompile.compile in file "toplevel/ccompile.ml" (inlined), line 96, characters 2-59
Called from Ccompile.compile_file in file "toplevel/ccompile.ml", line 105, characters 4-61
Called from Coqc.coqc_main in file "toplevel/coqc.ml", line 38, characters 2-100
Called from Coqc.coqc_run in file "toplevel/coqc.ml", line 54, characters 4-36
*)
