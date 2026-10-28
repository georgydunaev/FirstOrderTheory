(* Example 1: Simple First-Order Logic Example *)

Require Import Logic.FirstOrderLogic.

Definition example_predicate (x: nat) := x > 0.

Definition example_formula := forall x, example_predicate x.

Check example_formula.