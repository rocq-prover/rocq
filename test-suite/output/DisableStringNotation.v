Require Import Corelib.Strings.PrimString.
Import PStringNotations.

Inductive test_type : Set :=
| C1 | C2.

Definition parse1 : string -> test_type := fun _ => C1.
Definition parse2 : string -> test_type := fun _ => C2.

Definition print1 : test_type -> string := fun _ => "C1"%pstring.
Definition print2 : test_type -> string := fun _ => "C2"%pstring.

String Notation test_type parse1 print1 : core_scope.

Definition d1 := C1.
Definition d2 := C2.

Print d1.
Print d2.

String Notation test_type parse2 print2 : core_scope.

Print d1.
Print d2.

Disable String Notation parse2 : core_scope.

Print d1.
Print d2.

Disable String Notation parse1 : core_scope.

Print d1.
Print d2.

Enable String Notation parse2 : core_scope.

Print d1.
Print d2.

Enable String Notation parse1 : core_scope.

Print d1.
Print d2.
