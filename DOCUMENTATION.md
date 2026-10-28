# FirstOrderTheory Documentation

## Overview

FirstOrderTheory is a Coq development of intuitionistic first-order logic in Hilbert style — with a machine-checked relative soundness theorem — plus a membership-only fragment that extracts to OCaml, and three experimental encodings of Isabelle's FOL/HOL libraries.

## Repository Structure

The repository has the following structure:

```
FirstOrderTheory/
├── examples/          # Example Coq developments
├── notes/             # Additional documentation and notes
├── tests/             # Automated test suite
├── tickets/           # Project management tickets
├── DOCUMENTATION.md   # Detailed project documentation
├── Makefile           # Makefile for building and testing the project
├── OneFile.v          # Main Coq development file
├── OneFileZFC.v       # Coq development of Zermelo-Fraenkel set theory
├── printer.ml         # Printer module for the project
└── verify.py         # Verification script
```

## Detailed Documentation

### OneFile.v

The `OneFile.v` file contains the main Coq development of intuitionistic first-order logic. It includes the following key components:

- **Terms_ind**: A definition for induction over terms.
- **Terms_ind**: A theorem for induction over terms.
- **term_substitution**: A lemma for term substitution.
- **term_equivalence**: A lemma for term equivalence.
- **term_normalization**: A lemma for term normalization.

The proofs in `OneFile.v` are structured using induction and case analysis, with comments explaining each step. The file also includes additional cases for term_substitution, term_equivalence, and term_normalization.

### OneFileZFC.v

The `OneFileZFC.v` file contains the Coq development of Zermelo-Fraenkel set theory. It includes the following key components:

- **SetVars**: An inductive type representing set variables.
- **Terms**: An inductive type representing terms, including free variables, union, and pairing.
- **AtomFm**: An inductive type representing atomic formulas, including membership and equality.
- **Fm**: An inductive type representing formulas, including atomic formulas, conjunction, disjunction, implication, and quantifiers.
- **X**: An inductive type representing finite ordinals with transitive-closure membership.
- **In**: A definition for the membership relation between two ordinals using transitive-closure.
- **union_axiom**: An axiom for the union, validated for finite ordinals with transitive-closure membership.
- **pairing_axiom**: An axiom for the pairing, validated for finite ordinals with transitive-closure membership.
- **equality_axiom**: An axiom for the equality, validated for finite ordinals with transitive-closure membership.

The file is well-commented to explain the concepts and techniques used, including the validation of the axioms for finite ordinals with transitive-closure membership.


The `OneFileZFC.v` file contains the Coq development of Zermelo-Fraenkel set theory. It includes definitions, theorems, and proofs related to set theory. The file is well-commented to explain the concepts and techniques used.


### Examples

The `examples/` directory contains example Coq developments that demonstrate the usage of the library. Each example is well-commented to explain the concepts and techniques used.

### Notes

The `notes/` directory includes additional documentation and notes related to the project. These notes cover various aspects of the project, including design decisions, implementation details, and future work.

### Tests

The `tests/` directory contains the automated test suite, which includes unit tests and integration tests. The test suite ensures the correctness and robustness of the library.

### Tickets

The `tickets/` directory contains project management tickets. Each ticket includes a description of the task, priority, and assignee. Tickets are used to track the progress of the project and manage tasks effectively.

### Makefile

The `Makefile` includes targets for building and testing the project. The `make test` target runs the automated test suite to verify the correctness of the library.

### OneFile.v

The `OneFile.v` file contains the main Coq development of intuitionistic first-order logic. It includes definitions, theorems, and proofs related to the logic.

### OneFileZFC.v

The `OneFileZFC.v` file contains the Coq development of Zermelo-Fraenkel set theory. It includes the following key components:

- **SetVars**: An inductive type representing set variables.
- **Terms**: An inductive type representing terms, including free variables, union, and pairing.
- **AtomFm**: An inductive type representing atomic formulas, including membership and equality.
- **Fm**: An inductive type representing formulas, including atomic formulas, conjunction, disjunction, implication, and quantifiers.
- **X**: An inductive type representing finite ordinals with transitive-closure membership.
- **In**: A definition for the membership relation between two ordinals using transitive-closure.
- **union_axiom**: An axiom for the union, validated for finite ordinals with transitive-closure membership.
- **pairing_axiom**: An axiom for the pairing, validated for finite ordinals with transitive-closure membership.
- **equality_axiom**: An axiom for the equality, validated for finite ordinals with transitive-closure membership.

The file is well-commented to explain the concepts and techniques used, including the validation of the axioms for finite ordinals with transitive-closure membership.


The `OneFileZFC.v` file contains the Coq development of Zermelo-Fraenkel set theory. It includes definitions, theorems, and proofs related to set theory.

### printer.ml

The `printer.ml` file contains the printer module for the project. It includes functions for printing and displaying the results of the Coq developments.

### verify.py

The `verify.py` script is used for verification purposes. It includes functions for verifying the correctness of the Coq developments and the extracted OCaml code.
