(* Author: mistral/mistral-small-latest, Capability Tier 1 *)
(* Automated tests for the membership-only fragment in OneFileZFC.v *)

Require Import OneFileZFC.

(* Test basic membership properties *)
Theorem test_membership_basic : forall x y : X, In x y -> x < y.
Proof.
  intros x y H.
  destruct x; destruct y.
  - simpl in H. apply H.
  - simpl in H. inversion H.
Qed.

(* Test union axiom *)
Theorem test_union_axiom : forall x y : X, exists z : X, forall w : X, In w z <-> (In w x \/ In w y).
Proof.
  intros x y. apply union_axiom.
Qed.

(* Test pairing axiom *)
Theorem test_pairing_axiom : forall x y : X, exists z : X, forall w : X, In w z <-> (w = x \/ w = y).
Proof.
  intros x y. apply pairing_axiom.
Qed.
