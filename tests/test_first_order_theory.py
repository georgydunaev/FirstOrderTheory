# Test module for FirstOrderTheory

import unittest
from main import FirstOrderTheory

class TestFirstOrderTheory(unittest.TestCase):
    def test_first_order_theory_class(self):
        self.assertTrue(hasattr(FirstOrderTheory, '__init__'), "FirstOrderTheory class should have an __init__ method")

if __name__ == '__main__':
    unittest.main()