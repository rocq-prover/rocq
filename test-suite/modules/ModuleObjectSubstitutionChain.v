(* Regression coverage for substitution of algebraic module objects.

   The combined module type below deliberately retains references to many
   component module types. Loading it as a functor parameter therefore drives
   [Declaremods.subst_aobjs] through [Libobject.Ref] nodes and composes their
   substitutions with [Mod_subst.join]. The body of [Probe] is empty so the
   test isolates parameter loading from subsequent elaboration. *)

Module Type S00. Parameter t00 : Type. End S00.
Module Type S01. Parameter t01 : Type. End S01.
Module Type S02. Parameter t02 : Type. End S02.
Module Type S03. Parameter t03 : Type. End S03.
Module Type S04. Parameter t04 : Type. End S04.
Module Type S05. Parameter t05 : Type. End S05.
Module Type S06. Parameter t06 : Type. End S06.
Module Type S07. Parameter t07 : Type. End S07.
Module Type S08. Parameter t08 : Type. End S08.
Module Type S09. Parameter t09 : Type. End S09.
Module Type S10. Parameter t10 : Type. End S10.
Module Type S11. Parameter t11 : Type. End S11.
Module Type S12. Parameter t12 : Type. End S12.
Module Type S13. Parameter t13 : Type. End S13.
Module Type S14. Parameter t14 : Type. End S14.
Module Type S15. Parameter t15 : Type. End S15.
Module Type S16. Parameter t16 : Type. End S16.
Module Type S17. Parameter t17 : Type. End S17.
Module Type S18. Parameter t18 : Type. End S18.
Module Type S19. Parameter t19 : Type. End S19.
Module Type S20. Parameter t20 : Type. End S20.
Module Type S21. Parameter t21 : Type. End S21.
Module Type S22. Parameter t22 : Type. End S22.
Module Type S23. Parameter t23 : Type. End S23.
Module Type S24. Parameter t24 : Type. End S24.
Module Type S25. Parameter t25 : Type. End S25.
Module Type S26. Parameter t26 : Type. End S26.
Module Type S27. Parameter t27 : Type. End S27.
Module Type S28. Parameter t28 : Type. End S28.
Module Type S29. Parameter t29 : Type. End S29.
Module Type S30. Parameter t30 : Type. End S30.
Module Type S31. Parameter t31 : Type. End S31.
Module Type S32. Parameter t32 : Type. End S32.
Module Type S33. Parameter t33 : Type. End S33.
Module Type S34. Parameter t34 : Type. End S34.
Module Type S35. Parameter t35 : Type. End S35.
Module Type S36. Parameter t36 : Type. End S36.
Module Type S37. Parameter t37 : Type. End S37.
Module Type S38. Parameter t38 : Type. End S38.
Module Type S39. Parameter t39 : Type. End S39.

Module Type Nested.
  Parameter carrier : Type.
  Parameter value : carrier.
End Nested.

Module Type Structured.
  Inductive wrapped : Type := Wrap : nat -> wrapped.
  Declare Module Inner : Nested.
  Definition unwrap (x : wrapped) : nat :=
    match x with Wrap n => n end.
End Structured.

Module Type WithNested.
  Declare Module N : Nested.
End WithNested.

Module ConcreteNested.
  Definition carrier := nat.
  Definition value := 0.
End ConcreteNested.

Module ObjectSource.
  Definition value := 0.
  Abbreviation object_zero := value.
End ObjectSource.

(* Module aliases retain substitutive object references. Keeping many of them
   under one component makes parameter loading exercise repeated [Ref]
   composition without relying on an external plugin. *)
Module Type AliasObjects.
  Module Alias00 := ObjectSource.
  Module Alias01 := ObjectSource.
  Module Alias02 := ObjectSource.
  Module Alias03 := ObjectSource.
  Module Alias04 := ObjectSource.
  Module Alias05 := ObjectSource.
  Module Alias06 := ObjectSource.
  Module Alias07 := ObjectSource.
  Module Alias08 := ObjectSource.
  Module Alias09 := ObjectSource.
  Module Alias10 := ObjectSource.
  Module Alias11 := ObjectSource.
  Module Alias12 := ObjectSource.
  Module Alias13 := ObjectSource.
  Module Alias14 := ObjectSource.
  Module Alias15 := ObjectSource.
  Module Alias16 := ObjectSource.
  Module Alias17 := ObjectSource.
  Module Alias18 := ObjectSource.
  Module Alias19 := ObjectSource.
  Module Alias20 := ObjectSource.
  Module Alias21 := ObjectSource.
  Module Alias22 := ObjectSource.
  Module Alias23 := ObjectSource.
End AliasObjects.

Module Type ConstrainedNested :=
  WithNested with Module N := ConcreteNested.

Module Type Args :=
  S00 <+ S01 <+ S02 <+ S03 <+ S04 <+ S05 <+ S06 <+ S07 <+ S08 <+ S09 <+
  S10 <+ S11 <+ S12 <+ S13 <+ S14 <+ S15 <+ S16 <+ S17 <+ S18 <+ S19 <+
  S20 <+ S21 <+ S22 <+ S23 <+ S24 <+ S25 <+ S26 <+ S27 <+ S28 <+ S29 <+
  S30 <+ S31 <+ S32 <+ S33 <+ S34 <+ S35 <+ S36 <+ S37 <+ S38 <+ S39 <+
  Structured <+ ConstrainedNested <+ AliasObjects.

Module Type Probe (args : Args).
End Probe.

(* Replaying parameter loading after rollback must preserve the same result. *)
Module Type ProbeReplay (args : Args).
End ProbeReplay.
Reset ProbeReplay.
Module Type ProbeReplay (args : Args).
End ProbeReplay.

(* Applied functors and includes exercise the same composed substitution after
   the parameter has been accepted. *)
Module UseArgs (args : Args).
  Include args.
  Definition witness : t00 -> t00 := fun x => x.
End UseArgs.

Module ConcreteArgs <: Args.
  Definition t00 := nat.
  Definition t01 := nat.
  Definition t02 := nat.
  Definition t03 := nat.
  Definition t04 := nat.
  Definition t05 := nat.
  Definition t06 := nat.
  Definition t07 := nat.
  Definition t08 := nat.
  Definition t09 := nat.
  Definition t10 := nat.
  Definition t11 := nat.
  Definition t12 := nat.
  Definition t13 := nat.
  Definition t14 := nat.
  Definition t15 := nat.
  Definition t16 := nat.
  Definition t17 := nat.
  Definition t18 := nat.
  Definition t19 := nat.
  Definition t20 := nat.
  Definition t21 := nat.
  Definition t22 := nat.
  Definition t23 := nat.
  Definition t24 := nat.
  Definition t25 := nat.
  Definition t26 := nat.
  Definition t27 := nat.
  Definition t28 := nat.
  Definition t29 := nat.
  Definition t30 := nat.
  Definition t31 := nat.
  Definition t32 := nat.
  Definition t33 := nat.
  Definition t34 := nat.
  Definition t35 := nat.
  Definition t36 := nat.
  Definition t37 := nat.
  Definition t38 := nat.
  Definition t39 := nat.
  Inductive wrapped : Type := Wrap : nat -> wrapped.
  Module Inner := ConcreteNested.
  Definition unwrap (x : wrapped) : nat :=
    match x with Wrap n => n end.
  Module N := ConcreteNested.
  Module Alias00 := ObjectSource.
  Module Alias01 := ObjectSource.
  Module Alias02 := ObjectSource.
  Module Alias03 := ObjectSource.
  Module Alias04 := ObjectSource.
  Module Alias05 := ObjectSource.
  Module Alias06 := ObjectSource.
  Module Alias07 := ObjectSource.
  Module Alias08 := ObjectSource.
  Module Alias09 := ObjectSource.
  Module Alias10 := ObjectSource.
  Module Alias11 := ObjectSource.
  Module Alias12 := ObjectSource.
  Module Alias13 := ObjectSource.
  Module Alias14 := ObjectSource.
  Module Alias15 := ObjectSource.
  Module Alias16 := ObjectSource.
  Module Alias17 := ObjectSource.
  Module Alias18 := ObjectSource.
  Module Alias19 := ObjectSource.
  Module Alias20 := ObjectSource.
  Module Alias21 := ObjectSource.
  Module Alias22 := ObjectSource.
  Module Alias23 := ObjectSource.
End ConcreteArgs.

Module Applied := UseArgs ConcreteArgs.
Check Applied.witness.
