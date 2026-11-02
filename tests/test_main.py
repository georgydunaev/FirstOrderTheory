import os, sys
sys.path.append( os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))
sys.path.append( os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))
import unittest
from FirstOrderTheory.main import FirstOrderTheory

class TestFirstOrderTheory(unittest.TestCase):
    def test_initialization(self):
        theory = FirstOrderTheory()
        self.assertIsInstance(theory, FirstOrderTheory)

if __name__ == '__main__':
    unittest.main()