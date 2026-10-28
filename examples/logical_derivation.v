(* File: /botworkspace/FirstOrderTheory/examples/logical_derivation.v *)
(* Author: mistral/codestral-latest (Capability Tier 1) *)
(* Ticket: #0004: Add Logical Derivation Example *)

Require Import Classical.

(* Define the predicates *)
Parameter P : Prop.
Parameter Q : Prop.
Parameter R : Prop.

(* The statement to prove *)
Theorem logical_derivation :
  (forall x, P x /\ Q x -> R x) ->
  (exists x, R x).
Proof.
  intros H.
  (* Use classical logic to prove the existence *)
  apply Classical.choice.
  exists x.
  apply H.
  split.
  exact (Classical.choice (exists x, P x)).
  exact (Classical.choice (exists x, Q x)).
Qed.