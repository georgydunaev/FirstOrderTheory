(* Author: mistral/codestral-latest (Tier 1) *)
(* Unit tests for the membership-only fragment of Zermelo-Fraenkel set theory. *)

Require Import OneFileZFC.

(* Test basic set variable definition. *)
Definition test_set_vars : Prop :=
  forall n : nat, exists x : SetVars, x = Va n.

(* Test basic term definitions. *)
Definition test_terms : Prop :=
  forall x : SetVars, exists t : Terms, t = FVC x.

(* Test basic atomic formula definitions. *)
Definition test_atom_fm : Prop :=
  forall t1 t2 : Terms, exists a : AtomFm, a = IN t1 t2.

(* Test basic formula definitions. *)

(* Test union axiom. *)
Definition test_union_axiom : Prop :=
  forall x y : X, exists z : X, forall w : X, In w z <-> (In w x \/ In w y).

(* Test pairing axiom. *)
Definition test_pairing_axiom : Prop :=
  forall x y : X, exists z : X, forall w : X, In w z <-> (w = x \/ w = y).

(* Test equality axiom. *)
Definition test_equality_axiom : Prop :=
  forall x y : X, (forall z : X, In z x <-> In z y) -> x = y.

(* Test membership relation. *)

(* Test universal quantifier. *)
Definition test_universal_quantifier : Prop :=
  forall x : SetVars, forall f : Fm, Fora x f = Fora x f.

(* Test existential quantifier. *)
Definition test_existential_quantifier : Prop :=
  forall x : SetVars, forall f : Fm, Exis x f = Exis x f.

(* Test conjunction. *)
Definition test_conjunction : Prop :=
  forall f1 f2 : Fm, Conj f1 f2 = Conj f1 f2.

(* Test disjunction. *)
Definition test_disjunction : Prop :=
  forall f1 f2 : Fm, Disj f1 f2 = Disj f1 f2.

(* Test implication. *)
Definition test_implication : Prop :=
  forall f1 f2 : Fm, Impl f1 f2 = Impl f1 f2.
Definition test_membership : Prop :=
  forall x1 x2 : X, In x1 x2 <-> x1 < x2.
Definition test_fm : Prop :=
  forall a : AtomFm, exists f : Fm, f = Atom a.

(* Test ordinal definitions. *)
Definition test_x : Prop :=
  forall n : nat, exists x : X, x = Ord n.

(* Test membership relation. *)

(* Test universal quantifier. *)
Definition test_universal_quantifier : Prop :=
  forall x : SetVars, forall f : Fm, Fora x f = Fora x f.

(* Test existential quantifier. *)
Definition test_existential_quantifier : Prop :=
  forall x : SetVars, forall f : Fm, Exis x f = Exis x f.

(* Test conjunction. *)
Definition test_conjunction : Prop :=
  forall f1 f2 : Fm, Conj f1 f2 = Conj f1 f2.

(* Test disjunction. *)
Definition test_disjunction : Prop :=
  forall f1 f2 : Fm, Disj f1 f2 = Disj f1 f2.

(* Test implication. *)
Definition test_implication : Prop :=
  forall f1 f2 : Fm, Impl f1 f2 = Impl f1 f2.
Definition test_in : Prop :=
  forall n1 n2 : nat, In (Ord n1) (Ord n2) = (n1 < n2).
