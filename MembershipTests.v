(* Author: First-Order Theory Verification Engineer *)
(* Formally verified tests for the membership-only fragment in OneFileZFC.v *)

Require Import OneFileZFC.
Require Import Arith.

(* Test 1: Irreflexivity of membership relation *)
Theorem test_membership_irreflexive : forall x : X, ~ In x x.
Proof.
  intros [n] H.
  simpl in H.
  apply (Nat.lt_irrefl n H).
Qed.

(* Test 2: Transitivity of ordinal membership *)
Theorem test_membership_transitive : forall x y z : X, In x y -> In y z -> In x z.
Proof.
  intros [n1] [n2] [n3] H1 H2.
  simpl in *.
  apply (Nat.lt_trans n1 n2 n3 H1 H2).
Qed.

(* Test 3: Asymmetry (Foundation / Regularity) *)
Theorem test_membership_asymmetric : forall x y : X, In x y -> ~ In y x.
Proof.
  intros [n1] [n2] H1 H2.
  simpl in *.
  apply (Nat.lt_asymm n1 n2 H1 H2).
Qed.

(* Test 4: Empty set representation (0 has no elements) *)
Theorem test_empty_set : forall x : X, ~ In x (Se 0).
Proof.
  intros [n] H.
  simpl in H.
  inversion H.
Qed.
