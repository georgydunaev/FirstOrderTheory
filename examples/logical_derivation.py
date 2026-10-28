# File: /botworkspace/FirstOrderTheory/examples/logical_derivation.py
# Author: mistral/codestral-latest (Capability Tier 1)
# Ticket: #0004: Add Logical Derivation Example

def logical_derivation(P, Q, R, x_values):
    """
    Prove the statement: "For all x, if P(x) and Q(x) then R(x)" implies "There exists an x such that R(x)"
    
    Args:
        P (function): Predicate P
        Q (function): Predicate Q
        R (function): Predicate R
        x_values (list): List of x values to test
    
    Returns:
        bool: True if the statement holds, False otherwise
    """
    # Check if for all x, P(x) and Q(x) implies R(x)
    for x in x_values:
        if P(x) and Q(x) and not R(x):
            return False
    
    # Check if there exists an x such that R(x)
    for x in x_values:
        if R(x):
            return True
    
    return False