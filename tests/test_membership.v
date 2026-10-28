(* Author: mistral/mistral-medium-latest, Capability Tier 1 *)
(* Unit tests for membership-only fragment in OneFileZFC.v *)

Require Import OneFileZFC.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.

(* Test basic membership relation *)
Lemma test_membership_basic : forall n1 n2 : nat, n1 < n2 -> In (Ord n1) (Ord n2).
Proof.
  intros n1 n2 H.
  unfold In.
  simpl.
  exact H.
Qed.

(* Test membership with reflexivity *)
Lemma test_membership_reflexivity : forall n : nat, ~ In (Ord n) (Ord n).
Proof.
  intros n.
  unfold In.
  simpl.
  intros contra.
  apply Nat.lt_irrefl in contra.
  exact contra.
Qed.

(* Test membership with transitivity *)
Lemma test_membership_transitivity : forall n1 n2 n3 : nat, n1 < n2 -> n2 < n3 -> In (Ord n1) (Ord n3).
Proof.
  intros n1 n2 n3 H1 H2.
  unfold In.
  simpl.
  apply Nat.lt_trans in H1 H2.
  exact H1.
Qed.
