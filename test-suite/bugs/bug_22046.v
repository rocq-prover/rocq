Require Corelib.Setoids.Setoid.
Export Corelib.Classes.Morphisms.
Export Corelib.Setoids.Setoid.

Axiom fold_right : forall [A B : Type], (B -> A -> A) -> A.

Axiom pointwise2_relation :
forall (A A' : Type) {B : Type}, relation B -> (A -> A' -> B) -> (A -> A' -> B) -> Prop.

Declare Instance pointwise2_subrelation {A A' B} (R : relation B) :
  subrelation (pointwise2_relation A A' R) (pointwise_relation A (pointwise_relation A' R)).
Declare Instance pointwise2_forall_relation_inv {A A' B} (R : relation B) :
  subrelation (forall_relation (fun _ : A => forall_relation (fun _ : A' => R))) (pointwise2_relation A A' R).

Declare Instance fold_right_pointwise2eq_eq_eq_morphism : forall {A B : Type},
Proper (@pointwise2_relation B A _ eq ==> eq) (@fold_right A B).

(* Non-trivial TC problem requiring a precise sequentialization of evar solving *)
Goal forall (A B : Type) (f g : A -> B -> A),
  pointwise2_relation A B eq f g ->
  fold_right (fun (y : B) (x : A) => f x y) =
  fold_right (fun (y : B) (x : A) => g x y).
Proof.
intros.
setoid_rewrite H.
Abort.
