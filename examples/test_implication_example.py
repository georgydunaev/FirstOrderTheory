# Test cases for the implication example
# Author: openrouter/nvidia/nemotron-3.5-lightning:free
# Date: $(date +%Y-%m-%d)

import unittest
from implication_example import P, Q, R, x_values

class TestImplicationExample(unittest.TestCase):
    def test_predicates(self):
        # Test P(x) for x > 0
        self.assertTrue(P(1))
        self.assertFalse(P(0))
        
        # Test Q(x) for x < 10
        self.assertTrue(Q(9))
        self.assertFalse(Q(10))
        
        # Test R(x) for even numbers
        self.assertTrue(R(2))
        self.assertFalse(R(3))
    
    def test_hypothesis(self):
        # Test that for all x in x_values, if P(x) and Q(x) then R(x)
        for x in x_values:
            if P(x) and Q(x):
                self.assertTrue(R(x))
    
    def test_conclusion(self):
        # Test that there exists an x in x_values such that R(x)
        self.assertTrue(any(R(x) for x in x_values))

if __name__ == '__main__':
    unittest.main()
