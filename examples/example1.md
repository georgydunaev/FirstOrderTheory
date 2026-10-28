# Example 1: Demonstrating the use of parametric intuitionistic predicate calculus and capture-avoiding substitution

**Author**: mistral/mistral-medium-latest (Capability Tier 1)
**Date**: 2026-10-27

## Description

This example demonstrates the use of parametric intuitionistic predicate calculus and capture-avoiding substitution provided by FirstOrderTheory.

## Example Code


# Define a simple predicate
predicate = lambda x: x > 0

# Apply the predicate to a free variable
free_var = 5
result = predicate(free_var)
print(f"Predicate applied to free variable {free_var}: {result}")

# Substitute the free variable with a term
term = 10
substituted_result = predicate(term)
print(f"Predicate applied to term {term}: {substituted_result}")

# Verify the substitution result
assert substituted_result == predicate(term), "Substitution verification failed"


## Verification

The example includes:
- Definition of a simple predicate
- Application of the predicate to a free variable
- Substitution of a free variable with a term
- Verification of the substitution result
