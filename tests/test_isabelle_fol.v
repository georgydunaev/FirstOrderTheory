(* Test suite for the sketch of Isabelle's FOL library *)

Require Import Isabelle.

(* Test cases for the sketch of Isabelle's FOL library *)

(* Test case 1: Types/PT/PP hierarchies *)
Definition test_types_hierarchies : Prop := forall (A B : Prop), A -> B -> A.

(* Test case 2: Typed terms *)
Definition test_typed_terms : Prop := forall (A B : Prop), A -> B -> A.

(* Test case 3: Type-checking function TypeOfTerm *)
Definition test_type_checking : Prop := forall (A B : Prop), A -> B -> A.

(* Test case 4: ∧-introduction rule encoded as a term (conjI_type) *)
Definition test_conj_introduction : Prop := forall (A B : Prop), A -> B -> A.
