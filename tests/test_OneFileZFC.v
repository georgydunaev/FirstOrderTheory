(* Automated tests for OneFileZFC.v *)

Require Import OneFileZFC.

(* Test membership relation for finite ordinals with transitive-closure membership. *)Lemma test_membership_relation : forall n1 n2 : nat, In (Ord n1) (Ord n2) = (n1 < n2).
Proof.
  intros n1 n2.
  simpl.
  destruct (Ord n1), (Ord n2).
  simpl.
  reflexivity.
Qed.

(* Test union axiom for finite ordinals with transitive-closure membership. *)Lemma test_union_axiom : forall x y : X, exists z : X, forall w : X, In w z <-> (In w x \/ In w y).
Proof.
  intros x y.
  destruct x, y.
  simpl.
  exists (Ord (max n1 n2)).
  intros w.
  destruct w.
  simpl.
  split.
  - intro H. destruct H.
    + left; assumption.
    + right; assumption.
  - intro H. destruct H.
    + left; assumption.
    + right; assumption.
Qed.

(* Test pairing axiom for finite ordinals with transitive-closure membership. *)Lemma test_pairing_axiom : forall x y : X, exists z : X, forall w : X, In w z <-> (w = x \/ w = y).
Proof.
  intros x y.
  destruct x, y.
  simpl.
  exists (Ord (max n1 n2)).
  intros w.
  destruct w.
  simpl.
  split.
  - intro H. destruct H.
    + left; assumption.
    + right; assumption.
  - intro H. destruct H.
    + left; assumption.
    + right; assumption.
Qed.

(* Test equality axiom for finite ordinals with transitive-closure membership. *)Lemma test_equality_axiom : forall x y : X, (forall z : X, In z x <-> In z y) -> x = y.
Proof.
  intros x y H.
  destruct x, y.
  simpl.
  rewrite H.
  reflexivity.
Qed.
