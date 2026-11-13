(* Logical Derivation Example: Demonstrating Proof Construction in FirstOrderTheory *)
(* Author: First-Order Theory Verification Engineer *)

Section LogicalDerivation.

Variable D : Set.
Variable d0 : D.
Variable P : D -> Prop.
Variable Q : D -> Prop.
Variable R : D -> Prop.

Hypothesis HP : P d0.
Hypothesis HQ : Q d0.

Theorem exists_R : (forall x : D, P x -> Q x -> R x) -> (exists x : D, R x).
Proof.
  intros H.
  exists d0.
  apply H.
  - exact HP.
  - exact HQ.
Qed.

End LogicalDerivation.
