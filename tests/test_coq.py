import os, sys
sys.path.append( os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))
sys.path.append( os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))
import unittest

class TestCoq(unittest.TestCase):
    def test_coq_development(self):
        # Test the Coq development in OneFile.v
        from FirstOrderTheory import OneFile

        # Add your test cases here
        self.assertTrue(True)

if __name__ == '__main__':
    unittest.main()