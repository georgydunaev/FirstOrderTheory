(* Logical Derivation Example in Coq *)
(* Ticket: #0004: Add Logical Derivation Example *)

Section LogicalDerivation.

Variable D : Set.
Variable d0 : D.
Variable P : D -> Prop.
Variable Q : D -> Prop.
Variable R : D -> Prop.

Hypothesis HP : P d0.
Hypothesis HQ : Q d0.

Theorem logical_derivation : (forall x : D, P x -> Q x -> R x) -> (exists x : D, R x).
Proof.
  intros H.
  exists d0.
  apply H.
  - exact HP.
  - exact HQ.
Qed.

End LogicalDerivation.
