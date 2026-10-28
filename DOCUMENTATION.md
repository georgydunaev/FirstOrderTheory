# FirstOrderTheory Documentation

## Project Overview

FirstOrderTheory is a Coq development of intuitionistic first-order logic in Hilbert style. It includes a machine-checked relative soundness theorem and a membership-only fragment that extracts to OCaml. There are also experimental encodings of Isabelle's FOL/HOL libraries.

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

## Installation

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

## Usage

To use the project, you can run the Coq development files using the CoqIDE or the Coq proof assistant. The main development file is `OneFile.v`.

## Automated Test Suite

The project includes an automated test suite in the `tests/` directory. To run the tests, use the following command:

```
make test
```

## Contributing

Contributions are welcome! Please follow the guidelines in the [CONTRIBUTING.md](CONTRIBUTING.md) file for more information on how to contribute to the project.

Contributions are welcome! Please follow the guidelines in the `CONTRIBUTING.md` file for more information on how to contribute to the project.

The `Makefile` includes the following targets:

- `all`: Compiles the project and runs tests.
- `compile`: Compiles the Coq files.
- `test`: Runs the Python tests.
- `go`: Compiles and runs the OCaml program.

Contributions are welcome! Please follow the guidelines in the `CONTRIBUTING.md` file.

## License

This project is licensed under the MIT License. See the `LICENSE` file for details.

## Examples

The repository includes several examples demonstrating the use of the first-order logic framework:

1. **Traffic Light Example**: A simple traffic light system modeled using the first-order logic. See `examples/traffic_light_example.v` and `notes/traffic_light_tutorial.md` for details.

## Tutorials

In addition to the examples, the repository provides tutorials to help users understand and apply the framework:

1. **Traffic Light Tutorial**: A step-by-step guide to modeling a traffic light system using the first-order logic. See `notes/traffic_light_tutorial.md` for details.


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
└── README.md          # Project README
```

## Key Components

### Main Development (OneFile.v)

The main development includes:

- Parametric intuitionistic predicate calculus
- Syntax and capture-avoiding substitution
- Semantics and Hilbert-style calculus
- Machine-checked soundness theorem

### Membership-Only Fragment (OneFileZFC.v)

The membership-only fragment includes:

- Definitions for SetVars, Terms, AtomFm, Fm, X, and In
- Axioms for union, pairing, and equality
- A membership model and validation of the ZFC fragment

### Experimental Encodings of Isabelle's FOL/HOL Libraries (Isabelle.v)

The experimental encodings include:

- Definitions for Types, PT, and PTT
- Comments referencing Isabelle's notation and logic

### Proof-Relevant Natural-Deduction/Hilbert Model (IsabelleAlt.v)

The proof-relevant model includes:

- Definitions for o, prop, and Prf
- Proof rules for metalogic and object logic
- Equality and propositional logic rules

## Hardware Requirements

The project requires a GPU with at least 6GB of VRAM for optimal performance. The recommended GPU is an NVIDIA GeForce GTX 1660 Ti Mobile or equivalent. For smaller models, a GPU with 4GB of VRAM may suffice.

## Conclusion

This documentation provides an overview of the FirstOrderTheory project, its structure, and key components. For more detailed information, refer to the individual files and comments within the repository.