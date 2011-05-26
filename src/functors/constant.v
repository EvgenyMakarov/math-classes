Require Import
    Morphisms RelationClasses Equivalence Setoid Basics
    categories abstract_algebra interfaces.functors.

Section constant_functor.
Context `{Category A} `{Category B}.
Context (b:B).

Notation F :=  (const b).
Global Instance: Fmap F := fun _ _ _ => cat_id.

Global Instance: forall a a':A, Setoid_Morphism (fmap F:(a ⟶ a') -> (F a ⟶ F a')).
Proof.
  intros; constructor; try apply _.
  intros ? ? ?; reflexivity.
Qed.

Global Instance ConstantFunctor : Functor (const b) (fun _ _ _ => cat_id) := {}.
Proof.
  reflexivity.
  intros; symmetry; compute; apply left_identity.
Qed.

End constant_functor.

Typeclasses Transparent const.

Section constant_transformation.
Context `{Category A} `{Category J}.
Context {a a': A}.

Global Instance constant_transformation {f:a⟶a'} : NaturalTransformation (const f:J->_).
Proof with reflexivity.
  intros ???. rewrite left_identity, right_identity...
Qed.

End constant_transformation.
