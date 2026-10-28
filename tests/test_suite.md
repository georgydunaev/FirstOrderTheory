# FirstOrderTheory Test Suite

## Purpose

The test suite verifies the correctness of the FirstOrderTheory development by:

1. Testing individual components in isolation
2. Validating the main soundness theorem
3. Ensuring proper extraction to OCaml
4. Checking repository structure and file organization

## Running Tests

To run all tests:
```bash
make test
```

To run specific test groups:
```bash
make test-predicate
make test-isabelle
make test-membership
```

## Test Organization

The test suite is organized as follows:

- `test_predicate_calculus.v`: Tests for the predicate calculus
- `test_isabelle_fol.v`: Tests for Isabelle's FOL library
- `test_isabelle_metalogic.v`: Tests for the metalogic model
- `test_membership_fragment.v`: Tests for the OCaml-extractable fragment
- `test_repo_structure.py`: Python tests for repository structure
- `test_cognition.py`: Tests for cognition utilities

## Adding New Tests

1. Create a new test file following the naming convention `test_<component>.v` or `test_<component>.py`
2. Add the test to the appropriate `make` target in the Makefile
3. Update this documentation if needed

## Test Coverage Goals

The test suite aims to cover:
- All major components of the development
- Edge cases and error conditions
- Performance characteristics
- Cross-component interactions
