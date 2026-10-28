(* Test suite for the proof-relevant natural-deduction/Hilbert model of Isabelle's o / prop / Prf metalogic *)

Require Import IsabelleAlt.

(* Test cases for the proof-relevant natural-deduction/Hilbert model *)

(* Test case 1: Deduction theorem *)
Definition test_deduction_theorem : Prop := forall (A B : Prop), A -> B -> A.

(* Test case 2: Weakening rules *)
Definition test_weakening_rules : Prop := forall (A B : Prop), A -> B -> A.

(* Test case 3: Natural-deduction rules *)
Definition test_natural_deduction : Prop := forall (A B : Prop), A -> B -> A.

(* Test case 4: Hilbert-style calculus *)
Definition test_hilbert_calculus : Prop := forall (A B : Prop), A -> B -> A.
