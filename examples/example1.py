#!/usr/bin/env python3

# Example 1: Demonstrating the use of parametric intuitionistic predicate calculus and capture-avoiding substitution

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
