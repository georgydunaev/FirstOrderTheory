(* Author: openrouter/nvidia/nemotron-3.5-lightning:free (Tier 1) *)
(* Tests for the membership-only fragment in OneFileZFC.v *)

Require Import OneFileZFC.
Require Import Coq.Unicode.Utf8_core.
Require Import Coq.Unicode.Utf8_tactics.

(* Test the membership relation for ordinals *)Definition test_membership : Prop :=
  forall x1 x2 : X,
  In x1 x2 = (match x1, x2 with
    | Ord n1, Ord n2 => n1 < n2
    | _, _ => false
  end).

(* Test the union axiom *)Definition test_union_axiom : Prop :=
  forall x y : X,
  exists z : X, forall w : X, In w z <-> (In w x \/ In w y).

(* Test the pairing axiom *)Definition test_pairing_axiom : Prop :=
  forall x y : X,
  exists z : X, forall w : X, In w z <-> (w = x \/ w = y).

(* Test the equality axiom *)Definition test_equality_axiom : Prop :=
  forall x y : X,
  (forall z : X, In z x <-> In z y) -> x = y.

(* Run the tests *)Theorem membership_tests :
  test_membership /
  test_union_axiom /
  test_pairing_axiom /
  test_equality_axiom.

Proof.
  split.
  - intros x1 x2. simpl. destruct x1; destruct x2; simpl; auto.
  - intros x y. apply union_axiom.
  - intros x y. apply pairing_axiom.
  - intros x y H. apply equality_axiom.
Qed.
