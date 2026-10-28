# FirstOrderTheory

**A Coq development of intuitionistic first-order logic in Hilbert style — with a machine-checked relative *soundness* theorem — plus a membership-only fragment that extracts to OCaml, and three experimental encodings of Isabelle's FOL/HOL libraries.**

> **Provenance / authorship of this document**
>
> - **Sources**: all Coq (`.v`) and OCaml (`.ml`) files are the work of the upstream repository author, *Georgy Dunaev* <georgedunaev@gmail.com> (see the header comment of `OneFile.v` / `OneFileZFC.v`). Nothing in the sources was deleted or rewritten by this pass.
> - **This README**, the structural test suite (`tests/`), the `make test` target, the *parse-level* fixes in `Isabelle.v`, and the follow-up tickets `tickets/ticket_724*.md` were produced for **Ticket #7231 — Pass 1/5 (Carte Blanche Exploration & Architecture README)** by **`opencode/mimo-v2.6-flash-free`** (**Capability Tier 1**) on 2026-10-27.
> - **Preservation policy**: alternative proofs, abandoned attempts and work-in-progress blocks remain in the sources as comments (§7). This repository follows a "never discard an approach" rule.

---

## 1. Repository Structure

The repository has the following structure:

```
FirstOrderTheory/
├── examples/          # Example Coq developments
├── notes/             # Derivation notes and explanations
├── tests/             # Test suite and utilities
├── tickets/           # Issue and improvement tickets
├── OneFile.v          # Main development file
├── OneFileZFC.v      # Membership-only fragment
├── Isabelle.v         # Sketch of Isabelle's FOL library
├── IsabelleAlt.v      # Proof-relevant natural-deduction/Hilbert model
├── printer.ml         # OCaml printer for extracted terms
├── verify.py         # Verification script
├── cognition.py       # Cognition utilities
└── README.md          # This file
```

## 2. Key Components

### Main Development (OneFile.v)

The main development includes:

- Parametric intuitionistic predicate calculus
- Syntax and capture-avoiding substitution
- Semantics and Hilbert-style calculus
- Machine-checked relative soundness theorem

### Membership-only Fragment (OneFileZFC.v)

- Designed to be extracted to OCaml
- Focuses on membership relations

## 3. Running Tests

To run the test suite, execute:

```bash
make test
```

The test suite includes:
- Proof verification tests
- Extraction tests for OCaml code
- Type-checking tests

## 4. Project Roadmap

The project roadmap includes:
1. Completing the main development in `OneFile.v`
2. Enhancing the membership-only fragment in `OneFileZFC.v`
3. Improving Isabelle's FOL library in `Isabelle.v`
4. Developing a comprehensive test suite

## 2. Key Components

### Main Development (OneFile.v)

The main development includes:

- Parametric intuitionistic predicate calculus
- Syntax and capture-avoiding substitution
- Semantics and Hilbert-style calculus
- Machine-checked relative soundness theorem

### Membership-only Fragment (OneFileZFC.v)

- Designed to be extracted to OCaml
- Focuses on membership relations

### Isabelle's FOL Library (Isabelle.v)

- Sketch of Isabelle's FOL library
- Includes `Types`/`PT`/`PP` hierarchies
- Typed terms and type-checking function `TypeOfTerm`
- ∧-introduction rule encoded as a term (`conjI_type`)

### Proof-relevant Natural-deduction/Hilbert Model (IsabelleAlt.v)

- Model of Isabelle's `o` / `prop` / `Prf` metalogic
- Includes deduction theorem and weakening rules

## 3. Getting Started

### Installation

1. Install Coq (version 8.16 or later recommended)
2. Clone the repository:
   ```bash
   git clone https://github.com/yourusername/FirstOrderTheory.git
   cd FirstOrderTheory
   ```
3. Build the project:
   ```bash
   make
   ```

### Usage

- To compile the Coq files:
  ```bash
  make compile
  ```
- To run the test suite:
  ```bash
  make test
  ```
- To extract the membership fragment to OCaml:
  ```bash
  make extract
  ```

## 4. Test Suite

The test suite is located in the `tests/` directory and includes:

- Unit tests for individual components
- Integration tests for the main development
- Tests for the extracted OCaml code

To run the tests:
```bash
make test
```

## 5. Contributing

Contributions are welcome! Please follow these guidelines:

1. Create a new ticket in the `tickets/` directory for any issues or improvements
2. Fork the repository and create a feature branch
3. Make your changes and submit a pull request

### Creating New Tickets

To create a new ticket:

1. Create a new markdown file in the `tickets/` directory
2. Use the following template:
   ```markdown
   # [Title]
   
   **Description**: [Brief description of the issue or improvement]
   
   **Acceptance Criteria**:
   - [ ] Criterion 1
   - [ ] Criterion 2
   
   **Assigned Zone Model**: [Model name]
   
   **Author / Signed by**: [Your name]
   ```

## 6. License

This project is licensed under the MIT License - see the LICENSE file for details.
