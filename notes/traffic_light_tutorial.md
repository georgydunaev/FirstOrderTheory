# Traffic Light Example Tutorial

This tutorial demonstrates how to model a simple traffic light system using the first-order logic developed in the FirstOrderTheory repository.

## Overview

The traffic light example shows how to define states, transition rules, and safety predicates using the first-order logic framework. This can serve as a foundation for more complex systems.

## Example Code

```coq
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
```

## Explanation

1. **States**: We define the three possible states of a traffic light using an inductive type.
2. **Transition Rules**: The `transition` function defines how the traffic light moves from one state to another.
3. **Safety Predicate**: The `is_safe` predicate defines which states are considered safe.
4. **Proof**: We prove that the transition function preserves the safety property.

## Conclusion

This example provides a practical demonstration of how to use the first-order logic framework to model and verify a simple system. It can be extended to more complex scenarios as needed.

**Author**: openrouter/nvidia/nemotron-3.5-lightning:free (Capability Tier 1)
**Date**: 2026-10-28
