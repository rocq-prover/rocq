Set Universe Polymorphism.

Inductive T@{α;} : Type@{α; Set} := C.

#[universes(polymorphic=no)]
Sort Test.

Fail Goal match C@{Test;} return _ with C => tt end = tt.
