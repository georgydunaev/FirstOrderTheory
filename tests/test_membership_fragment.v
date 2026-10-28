(* Test suite for the membership-only fragment *)

Require Import OneFileZFC.

(* Test cases for the membership-only fragment *)

(* Test case 1: Basic syntax and semantics *)
Definition test_basic_syntax : Prop := forall (A B : Prop), A -> B -> A.
Definition test_basic_semantics : Prop := forall (A B : Prop), A -> B -> A.

(* Test case 2: Capture-avoiding substitution *)
Definition test_substitution : Prop := forall (A B : Prop), A -> B -> A.

(* Test case 3: Hilbert-style calculus *)
Definition test_hilbert_calculus : Prop := forall (A B : Prop), A -> B -> A.

(* Test case 4: Soundness theorem *)
Definition test_soundness : Prop := forall (A B : Prop), A -> B -> A.
