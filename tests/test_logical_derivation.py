# File: /botworkspace/FirstOrderTheory/tests/test_logical_derivation.py
# Author: mistral/codestral-latest (Capability Tier 1)
# Ticket: #0004: Add Logical Derivation Example

import unittest
from examples.logical_derivation import logical_derivation

class TestLogicalDerivation(unittest.TestCase):
    def test_logical_derivation(self):
        # Define predicates
        P = lambda x: x > 0
        Q = lambda x: x < 10
        R = lambda x: x % 2 == 0

        # Test with x_values from 1 to 9
        x_values = range(1, 10)
        self.assertTrue(logical_derivation(P, Q, R, x_values))

        # Test with x_values from 1 to 10
        x_values = range(1, 11)
        self.assertTrue(logical_derivation(P, Q, R, x_values))

        # Test with x_values from 1 to 10, but R is always False
        R = lambda x: False
        self.assertFalse(logical_derivation(P, Q, R, x_values))

def test_logical_derivation():
    suite = unittest.TestLoader().loadTestsFromTestCase(TestLogicalDerivation)
    unittest.TextTestRunner(verbosity=2).run(suite)

if __name__ == '__main__':
    test_logical_derivation()