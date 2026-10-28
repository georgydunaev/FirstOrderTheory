# Test for Logical Derivation Example
# Author: openrouter/nvidia/nemotron-3.5-lightning:free (Capability Tier 1)
# Date: $(date +%Y-%m-%d)

import pytest
from examples.logical_derivation_example import P, Q, R, x_values

def test_predicate_definitions():
    """Test that the predicate definitions are correct"""
    assert P(5) == True
    assert Q(5) == True
    assert R(4) == True
    assert P(11) == False
    assert Q(11) == False
    assert R(3) == False


def test_hypothesis():
    """Test that the hypothesis holds for some x"""
    # Check if there exists at least one x where P(x) and Q(x) and R(x) are all True
    assert any(P(x) and Q(x) and R(x) for x in x_values)


def test_conclusion():
    """Test that the conclusion holds"""
    # Check if there exists at least one x where R(x) is True
    assert any(R(x) for x in x_values)

if __name__ == "__main__":
    pytest.main(["-v", "test_logical_derivation_example.py"])
