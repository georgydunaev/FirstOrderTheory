# Test module for FirstOrderTheory

import unittest
from main import FirstOrderTheory

class TestFirstOrderTheory(unittest.TestCase):
    def test_class_exists(self):
        self.assertTrue(hasattr(FirstOrderTheory, '__class__'))

if __name__ == '__main__':
    unittest.main()