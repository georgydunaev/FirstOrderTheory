(* Author: First-Order Theory Verification Engineer *)
(* Formally verified tests for the membership-only fragment in OneFileZFC.v *)

Require Import OneFileZFC.
Require Import Arith.

Definition test_membership : Prop :=
  forall n1 n2 : nat, In (Se n1) (Se n2) <-> n1 < n2.

Definition test_empty_set_property : Prop :=
  forall x : X, ~ In x (Se 0).

Definition test_transitivity_property : Prop :=
  forall x y z : X, In x y -> In y z -> In x z.

Definition test_irreflexivity_property : Prop :=
  forall x : X, ~ In x x.

Theorem membership_tests :
  test_membership /\
  test_empty_set_property /\
  test_transitivity_property /\
  test_irreflexivity_property.
Proof.
  split.
  - intros a b. simpl. reflexivity.
  - split.
    + intros [a] H. simpl in H. inversion H.
    + split.
      * intros [a] [b] [c] H1 H2. simpl in *. apply (Nat.lt_trans a b c H1 H2).
      * intros [a] H. simpl in H. apply (Nat.lt_irrefl a H).
Qed.
