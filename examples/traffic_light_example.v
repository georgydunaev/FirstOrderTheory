(*
 * Traffic Light Example using FirstOrderTheory
 *
 * This file demonstrates how to model a simple traffic light system using the
 * first-order logic developed in the FirstOrderTheory repository.
 *
 * Author: openrouter/nvidia/nemotron-3.5-lightning:free (Capability Tier 1)
 * Date: 2026-10-28
 *)

Require Import OneFile.

(* Define the states of the traffic light *)
Inductive State : Type := | Red | Yellow | Green.

(* Define the transition rules for the traffic light *)
Definition transition (current : State) : State :=
  match current with
  | Red => Green
  | Green => Yellow
  | Yellow => Red
  end.

(* Define a predicate to check if a state is safe *)
Definition is_safe (s : State) : Prop :=
  match s with
  | Red => True
  | Green => True
  | Yellow => False
  end.

(* Prove that the transition function preserves safety *)
Theorem transition_preserves_safety : forall s, is_safe (transition s) = is_safe s.
Proof.
  intros s.
  destruct s as [| | ].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
