# Test suite for FirstOrderTheory module

import unittest
from main import FirstOrderTheory

class TestFirstOrderTheory(unittest.TestCase):
    def test_initialization(self):
        theory = FirstOrderTheory()
        self.assertIsInstance(theory, FirstOrderTheory)

if __name__ == '__main__':
    unittest.main()