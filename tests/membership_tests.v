(* Author: mistral/codestral-latest (Tier 1) *)
(* Unit tests for the membership-only fragment in OneFileZFC.v *)

Require Import OneFileZFC.

(* Test cases for the membership relation In *)
Lemma test_In_1 : In (Ord 0) (Ord 1).
Proof.
  exact (In (Ord 0) (Ord 1)).
Qed.

Lemma test_In_2 : ~ In (Ord 1) (Ord 0).
Proof.
  exact (not (In (Ord 1) (Ord 0))).
Qed.

(* Test cases for the union axiom *)
Lemma test_union_axiom_1 : exists z : X, forall w : X, In w z <-> (In w (Ord 0) \/ In w (Ord 1)).
Proof.
  exists (Ord 2).
  intros w.
  split.
    - intros H. destruct H as [H0 | H1].
      + left. exact H0.
      + right. exact H1.
    - intros H. destruct H as [H0 | H1].
      + left. exact H0.
      + right. exact H1.
Qed.

(* Test cases for the pairing axiom *)
Lemma test_pairing_axiom_1 : exists z : X, forall w : X, In w z <-> (w = Ord 0 \/ w = Ord 1).
Proof.
  exists (Ord 2).
  intros w.
  split.
    - intros H. destruct H as [H0 | H1].
      + exact H0.
      + exact H1.
    - intros H. destruct H as [H0 | H1].
      + left. exact H0.
      + right. exact H1.
Qed.

(* Test cases for the equality axiom *)
Lemma test_equality_axiom_1 : forall x y : X, (forall z : X, In z x <-> In z y) -> x = y.
Proof.
  intros x y H.
  apply equality_axiom.
  exact H.
Qed.
