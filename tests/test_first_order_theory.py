# Test module for FirstOrderTheory

import unittest
from main import FirstOrderTheory

class TestFirstOrderTheory(unittest.TestCase):
    def test_instantiation(self):
        theory = FirstOrderTheory()
        self.assertIsInstance(theory, FirstOrderTheory)

if __name__ == '__main__':
    unittest.main()