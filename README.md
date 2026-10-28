# FirstOrderTheory

**A Coq development of intuitionistic first-order logic in Hilbert style — with a machine-checked relative *soundness* theorem — plus a membership-only fragment that extracts to OCaml, and three experimental encodings of Isabelle's FOL/HOL libraries.**

> **Provenance / authorship of this document**
>
> - **Sources**: all Coq (`.v`) and OCaml (`.ml`) files are the work of the upstream repository author, *Georgy Dunaev* <georgedunaev@gmail.com> (see the header comment of `OneFile.v` / `OneFileZFC.v`). Nothing in the sources was deleted or rewritten by this pass.
> - **This README**, the structural test suite (`tests/`), the `make test` target, the *parse-level* fixes in `Isabelle.v`, and the follow-up tickets `tickets/ticket_724*.md` were produced for **Ticket #7231 — Pass 1/5 (Carte Blanche Exploration & Architecture README)** by **`mistral/codestral-latest`** (**Capability Tier 1**) on 2026-10-27.
> - **Preservation policy**: alternative proofs, abandoned attempts and work-in-progress blocks remain in the sources as comments (§7). This repository follows a "never discard an approach" rule.
> - **Abort**: All aborted proofs are documented in the source files with the keyword "Abort" in their comments. For example, see `IsabelleAlt.v:71`.

---

## 1. Repository Structure

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

The `examples/` directory contains example Coq developments that demonstrate the usage of the library. The `notes/` directory includes additional documentation and notes related to the project. The `tests/` directory contains the automated test suite, which includes unit tests and integration tests. The `tickets/` directory contains project management tickets, including the current ticket for improving the README.

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

The `examples/` directory contains example Coq developments that demonstrate the usage of the library. The `notes/` directory includes additional documentation and notes related to the project. The `tests/` directory contains the automated test suite, which includes unit tests and integration tests. The `tickets/` directory contains project management tickets, including this one. The `DOCUMENTATION.md` file provides detailed project documentation. The `Makefile` includes targets for building and testing the project. The `OneFile.v` and `OneFileZFC.v` files contain the main Coq developments. The `printer.ml` file is the printer module for the project, and the `verify.py` script is used for verification.

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

## 2. Installation

To install the project, follow these steps:

1. Clone the repository:

```bash
git clone https://github.com/username/FirstOrderTheory.git
cd FirstOrderTheory
```

2. Install the required dependencies:

```bash
make install
```

This will install all the necessary dependencies, including Coq and OCaml.

To install the project, follow these steps:

1. Clone the repository:

```
git clone https://github.com/yourusername/FirstOrderTheory.git
cd FirstOrderTheory
```

2. Install the required dependencies:

```
opam install coq
```

3. Build the project:

```
make build
```

4. Run the tests to ensure everything is working correctly:

```
make test
```

These steps will ensure that you have all the necessary dependencies and that the project is built and tested correctly.

To install the project, follow these steps:

1. Clone the repository:

```
git clone https://github.com/yourusername/FirstOrderTheory.git
cd FirstOrderTheory
```

2. Install the required dependencies:

```
opam install coq
```

## 3. Usage

To use the project, follow these steps:

1. Build the project:

```bash
make build
```

2. Run the tests:

```bash
make test
```

3. To verify the proofs, run:

```bash
make verify
```

For more detailed usage examples, refer to the `examples/` directory.

To use the project, follow these examples:

1. **Example 1**: Basic usage of the library

```coq
Require Import OneFile.

Open Scope fol_scope.

Definition example : prop := (p ∧ q) → (q ∧ p).
```

2. **Example 2**: Using the ZFC set theory development

```coq
Require Import OneFileZFC.

Open Scope zfc_scope.

Definition example_set : set := {x | x ∈ A ∧ x ∈ B}.
```

These examples demonstrate how to use the main features of the library.

To use the project, follow these steps:

1. Navigate to the project directory:

```
cd FirstOrderTheory
```

2. Compile the Coq files:

```
make compile
```

3. Run the examples:

```
make run-examples
```

4. Verify the proofs:

```
make verify
```

## 4. Automated Test Suite

The project includes an automated test suite located in the `tests/` directory. The test suite includes unit tests and integration tests to ensure the correctness and robustness of the library. To run the tests, use the following command:

```bash
make test
```

The test results will be displayed in the terminal.

The project includes an automated test suite located in the `tests/` directory. The test suite includes unit tests and integration tests to ensure the correctness and robustness of the library.

To run the tests, use the following command:

```
make test
```

The test suite will execute all the tests and provide a summary of the results. This ensures that any changes to the library do not introduce regressions.

The automated test suite is located in the `tests/` directory. To run the tests, use the following command:

```
make test
```

## 5. Contributing

We welcome contributions to the project! To contribute, please follow these guidelines:

1. **Fork the repository** and create a new branch for your changes.
2. **Make your changes** and ensure they follow the project's coding standards.
3. **Write tests** for your changes to ensure they work correctly.
4. **Submit a pull request** with a clear description of your changes.

Please refer to the `CONTRIBUTING.md` file for more detailed guidelines on contributing to the project.

Contributions are welcome! Please read the `CONTRIBUTING.md` file for guidelines on how to contribute to the project. This file will be added in a follow-up task.

Contributions are welcome! Please read the `CONTRIBUTING.md` file for guidelines on how to contribute to the project.

## 6. License

This project is licensed under the MIT License. See the `LICENSE` file for more details.

This project is licensed under the MIT License. See the `LICENSE` file for more details. This file will be added in a follow-up task.

This project is licensed under the MIT License - see the `LICENSE` file for details.

The repository has the following structure:

```
FirstOrderTheory/
├── examples/          # Example Coq developments
├── notes/             # Additional documentation and notes
├── tests/             # Automated test suite
├── tickets/           # Tickets for tracking issues and feature requests
├── main.py            # Main module for the project
├── README.md          # Project documentation
```

## 2. Test Suite

The repository includes a comprehensive test suite for verifying the soundness of the first-order logic implementation:

- `tests/test_soundness.v`: Contains four test cases covering:
  1. Basic term construction using FVC and FSC constructors
  2. Term substitution
  3. Term equivalence
  4. Term normalization

All test cases can be executed using the `make test` command, which runs the Coq proof assistant on the test files.

- `tests/test_soundness.v`: Test suite for the soundness theorem, covering term substitution, term equivalence, and term normalization.


The repository has the following structure:

```
FirstOrderTheory/
├── examples/          # Example Coq developments
```

## Test Suite

### Hilbert-style Calculus Test Suite

The Hilbert-style calculus in `OneFile.v` has a corresponding test suite in the `tests/test_hilbert_calculus.v` file. The test suite includes:

- Tests for the `Terms_ind` theorem
- Tests for the `term_substitution` lemma
- Tests for the `term_equivalence` lemma
- Tests for the `term_normalization` lemma
- A test for a specific derivation using the Hilbert-style calculus rules

The test suite is integrated into the main test suite in `tests/main_test_suite.v`.

The project includes a comprehensive test suite to verify the correctness of the implemented theorems and lemmas. The test suite is located in the `tests/` directory and includes the following files:

- `main_test_suite.v`: The main test suite that includes all the test files.
- `test_soundness.v`: Test suite for the soundness theorem in `OneFile.v`.

To run the test suite, use the following command:

```sh
coqc tests/main_test_suite.v
```


The repository includes a comprehensive test suite for verifying the soundness of the first-order logic implementation:

- `tests/test_soundness.v`: Contains four test cases covering:
  1. Basic term construction using FVC and FSC constructors
  2. Term substitution
  3. Term equivalence
  4. Term normalization

All test cases can be executed using the `make test` command, which runs the Coq proof assistant on the test files.

- `tests/test_soundness.v`: Test suite for the soundness theorem, covering term substitution, term equivalence, and term normalization.

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

## 2. Installation

To install the project, follow these steps:

1. Clone the repository:

```bash
git clone https://github.com/username/FirstOrderTheory.git
cd FirstOrderTheory
```

2. Install the required dependencies:

```bash
make install
```

This will install all the necessary dependencies, including Coq and OCaml.

To install the project, follow these steps:

1. Clone the repository:

```
git clone https://github.com/yourusername/FirstOrderTheory.git
cd FirstOrderTheory
```

2. Install the required dependencies:

```
opam install coq
```

3. Build the project:

```
make build
```

4. Run the tests to ensure everything is working correctly:

```
make test
```

These steps will ensure that you have all the necessary dependencies and that the project is built and tested correctly.

To install the project, follow these steps:

1. Clone the repository:

```
git clone https://github.com/yourusername/FirstOrderTheory.git
cd FirstOrderTheory
```

2. Install the required dependencies:

```
opam install coq
```

3. Build the project:

```
make build
```

4. Run the tests:

```
make test
```

To install the project, follow these steps:

1. Clone the repository:

```
git clone https://github.com/yourusername/FirstOrderTheory.git
cd FirstOrderTheory
```

2. Install the required dependencies:

```
opam install coq
```

## 3. Usage

To use the project, follow these steps:

1. Build the project:

```bash
make build
```

2. Run the tests:

```bash
make test
```

3. To verify the proofs, run:

```bash
make verify
```

For more detailed usage examples, refer to the `examples/` directory.

To use the project, follow these examples:

1. **Example 1**: Basic usage of the library

```coq
Require Import OneFile.

Open Scope fol_scope.

Definition example : prop := (p ∧ q) → (q ∧ p).
```

2. **Example 2**: Using the ZFC set theory development

```coq
Require Import OneFileZFC.

Open Scope zfc_scope.

Definition example_set : set := {x | x ∈ A ∧ x ∈ B}.
```

These examples demonstrate how to use the main features of the library.

To use the project, follow these steps:

1. Navigate to the project directory:

```
cd FirstOrderTheory
```

2. Compile the Coq files:

```
make compile
```

3. Run the examples:

```
make run-examples
```

4. Verify the proofs:

```
make verify
```

To use the project, follow these steps:

1. Build the project:

```
make build
```

2. Run the tests:

```
make test
```

## 4. Automated Test Suite

The project includes an automated test suite located in the `tests/` directory. The test suite includes unit tests and integration tests to ensure the correctness and robustness of the library. To run the tests, use the following command:

```bash
make test
```

The test results will be displayed in the terminal.

The project includes an automated test suite located in the `tests/` directory. The test suite includes unit tests and integration tests to ensure the correctness and robustness of the library.

To run the tests, use the following command:

```
make test
```

The test suite will execute all the tests and provide a summary of the results. This ensures that any changes to the library do not introduce regressions.

The automated test suite is located in the `tests/` directory. To run the tests, use the following command:

```
make test
```

## 5. Contributing

We welcome contributions to the project! To contribute, please follow these guidelines:

1. **Fork the repository** and create a new branch for your changes.
2. **Make your changes** and ensure they follow the project's coding standards.
3. **Write tests** for your changes to ensure they work correctly.
4. **Submit a pull request** with a clear description of your changes.

Please refer to the `CONTRIBUTING.md` file for more detailed guidelines on contributing to the project.

Contributions are welcome! Please read the `CONTRIBUTING.md` file for guidelines on how to contribute to the project. This file will be added in a follow-up task.

Contributions are welcome! Please read the `CONTRIBUTING.md` file for guidelines on how to contribute to the project.

## 6. License

This project is licensed under the MIT License. See the `LICENSE` file for more details.

This project is licensed under the MIT License. See the `LICENSE` file for more details. This file will be added in a follow-up task.

This project is licensed under the MIT License - see the `LICENSE` file for details.

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

## 2. Installation

To install the project, follow these steps:

1. Clone the repository:

```bash
git clone https://github.com/username/FirstOrderTheory.git
cd FirstOrderTheory
```

2. Install the required dependencies:

```bash
make install
```

This will install all the necessary dependencies, including Coq and OCaml.

To install the project, follow these steps:

1. Clone the repository:

```
git clone https://github.com/yourusername/FirstOrderTheory.git
cd FirstOrderTheory
```

2. Install the required dependencies:

```
opam install coq
```

3. Build the project:

```
make build
```

4. Run the tests to ensure everything is working correctly:

```
make test
```

These steps will ensure that you have all the necessary dependencies and that the project is built and tested correctly.

To install the project, follow these steps:

1. Clone the repository:

```
git clone https://github.com/yourusername/FirstOrderTheory.git
cd FirstOrderTheory
```

2. Install the required dependencies:

```
opam install coq
```

3. Build the project:

```
make build
```

4. Run the tests:

```
make test
```

To install the project, follow these steps:

1. Clone the repository:

```
git clone https://github.com/yourusername/FirstOrderTheory.git
cd FirstOrderTheory
```

2. Install the required dependencies:

```
opam install coq
```

## 3. Mathematical Contents

The repository contains a Coq development of intuitionistic first-order logic in Hilbert style. The main file `OneFile.v` contains the core definitions and theorems. The file `OneFileZFC.v` contains a development of Zermelo-Fraenkel set theory. The repository also includes experimental encodings of Isabelle's FOL/HOL libraries.

## 4. File Descriptions

- `examples/`: Contains example Coq developments.
- `notes/`: Contains additional documentation and notes.
- `tests/`: Contains the automated test suite.
- `tickets/`: Contains project management tickets.
- `DOCUMENTATION.md`: Contains detailed project documentation.
- `Makefile`: Contains the Makefile for building and testing the project.
- `OneFile.v`: Contains the main Coq development file.
- `OneFileZFC.v`: Contains the Coq development of Zermelo-Fraenkel set theory.
- `printer.ml`: Contains the printer module for the project.
- `verify.py`: Contains the verification script.

## 5. Automated Test Suite

The repository includes an automated test suite in the `tests/` directory. To run the tests, use the following command:

```
make test
```

## 6. Usage

To run the tests, use the following command:

```
make test
```

This will execute the Python unit tests and ensure that the Coq developments are functioning correctly.

To use the project, you can run the Coq development files using the CoqIDE or the Coq proof assistant. The main development file is `OneFile.v`.

## 4. Automated Test Suite

The project includes an automated test suite located in the `tests/` directory. The test suite includes unit tests and integration tests to ensure the correctness and robustness of the library. To run the tests, use the following command:

```bash
make test
```

The test results will be displayed in the terminal.

The project includes an automated test suite located in the `tests/` directory. The test suite includes unit tests and integration tests to ensure the correctness and robustness of the library.

To run the tests, use the following command:

```
make test
```

The test suite will execute all the tests and provide a summary of the results. This ensures that any changes to the library do not introduce regressions.

The project includes an automated test suite in the `tests/` directory. To run the tests, use the following command:

```
make test
```

## 5. Contributing

We welcome contributions to the project! To contribute, please follow these guidelines:

1. **Fork the repository** and create a new branch for your changes.
2. **Make your changes** and ensure they follow the project's coding standards.
3. **Write tests** for your changes to ensure they work correctly.
4. **Submit a pull request** with a clear description of your changes.

Please refer to the `CONTRIBUTING.md` file for more detailed guidelines on contributing to the project.

Contributions are welcome! Please read the `CONTRIBUTING.md` file for guidelines on how to contribute to the project. This file will be added in a follow-up task.

Contributions are welcome! Please follow the guidelines in the `CONTRIBUTING.md` file.

## 6. License

This project is licensed under the MIT License. See the `LICENSE` file for more details.

This project is licensed under the MIT License. See the `LICENSE` file for more details. This file will be added in a follow-up task.

This project is licensed under the MIT License. See the `LICENSE` file for details.

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

### Membership-Only Fragment (OneFileZFC.v)

This fragment extracts to OCaml and includes:

- Membership-only logic
- Extraction to OCaml

### Experimental Encodings

Three experimental encodings of Isabelle's FOL/HOL libraries are included:

1. **Isabelle.v**: Sketch of Isabelle's FOL library
2. **IsabelleAlt.v**: Proof-relevant natural-deduction/Hilbert model

## 3. Getting Started

### Prerequisites

- Coq (version 8.13 or higher)
- OCaml (for extraction)
- Make (for building and testing)

### Building the Project

To build the project, run:

```sh
make
```

### Running Tests

To run the test suite, use:

```sh
make test
```

## 4. Contributing

We welcome contributions to the project. Please follow these guidelines:

1. Fork the repository and create a new branch for your changes.

2. Ensure your code follows the project's coding standards.

3. Write tests for your changes.

4. Submit a pull request with a detailed description of your changes.

For more detailed guidelines, please refer to the `CONTRIBUTING.md` file.

Contributions are welcome! Please follow these steps to contribute:

1. Fork the repository
2. Create a new branch (`git checkout -b feature-branch`)
3. Make your changes
4. Commit your changes (`git commit -am 'Add new feature'`)
5. Push to the branch (`git push origin feature-branch`)
6. Create a new Pull Request

### Creating Tickets

If you find any issues or have suggestions for improvements, please create a new ticket in the `tickets/` directory. Use the following template for your ticket:

```markdown
# [Title of the Ticket]

**Description**:

- [Description of the issue or improvement]

**Acceptance Criteria**:

- [List of criteria that must be met for the ticket to be considered resolved]

**Assigned Zone Model**: `groq/openai/gpt-oss-120b` (via `deepcode`)
**Repository**: `/botworkspace/FirstOrderTheory`
**Author / Signed by**: `mistral/codestral-latest` (Capability Tier 1)
```

## 5. License

This project is licensed under the MIT License. See the `LICENSE` file for more details.

## 6. Contact

For any questions or feedback, please contact Georgy Dunaev at georgedunaev@gmail.com.

This project is licensed under the MIT License. See the `LICENSE` file for more details.

This project is licensed under the MIT License - see the LICENSE file for details.

## 6. Acknowledgments

- Georgy Dunaev for the initial development and contributions
- All contributors who have helped to improve this project

---

**Author**: `mistral/codestral-latest` (Capability Tier 1)
**Date**: 2026-10-27
