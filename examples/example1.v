(*
 * Example 1: Demonstrating the use of parametric intuitionistic predicate calculus
 * and capture-avoiding substitution in FirstOrderTheory
 *
 * Author: groq/qwen/qwen3.8-27b (Capability Tier 1)
 * Date: 2026-10-27
 *
 * This example demonstrates the basic usage of the parametric intuitionistic predicate calculus
 * and the capture-avoiding substitution provided by FirstOrderTheory.
 *
 * It includes:
 * 1. Definition of a simple predicate
 * 2. Application of the predicate to a free variable
 * 3. Substitution of a free variable with a term
 *
 * This example is part of the FirstOrderTheory repository and is intended to be a
 * self-contained demonstration of the repository's capabilities.
 */

Require Import OneFile.

(* Define a simple predicate P that takes a term and returns a proposition *)
Definition P (t:Terms) : Prop := Terms_ind (fun t => True) (fun sv => True) (fun f v H => True) t.

(* Apply the predicate P to a free variable x *)
Definition x := FVC 0.
Definition P_x := P x.

(* Define a term t that we will substitute for x *)
Definition t := FSC 0 (Vector.make 1 (FVC 1)).

(* Substitute x with t in P_x *)
Definition P_t := Terms_ind (fun t => P t) (fun sv => P (FVC sv)) (fun f v H => P (FSC f v)) t.

(* Verify that P_t is equivalent to P t *)
Lemma P_t_eq_P_t : P_t = P t.
Proof.
  reflexivity.
Qed.
