# Test cases for the logical derivation example

import unittest
from logical_derivation import logical_derivation, P, Q, R

class TestLogicalDerivation(unittest.TestCase):
    def test_logical_derivation(self):
        result = logical_derivation()
        self.assertIsNotNone(result, "No x found such that R(x) holds")
        self.assertTrue(R(result), f"R({result}) should be True")

    def test_predicates(self):
        # Test P(x)
        self.assertTrue(P(2), "P(2) should be True")
        self.assertFalse(P(3), "P(3) should be False")
        
        # Test Q(x)
        self.assertTrue(Q(1), "Q(1) should be True")
        self.assertFalse(Q(0), "Q(0) should be False")
        
        # Test R(x)
        self.assertTrue(R(3), "R(3) should be True")
        self.assertFalse(R(4), "R(4) should be False")

if __name__ == "__main__":
    unittest.main()
