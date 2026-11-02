import os, sys
sys.path.append( os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))
sys.path.append( os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))
import unittest
from FirstOrderTheory import Terms, Terms_ind, FSV, Vector, term_substitution


class TestFirstOrderSuite(unittest.TestCase):
    def test_terms_ind(self):
        term = Terms.FVC("x")
        self.assertTrue(Terms_ind(lambda t: True, lambda sv: True, lambda f, v, ih: True, term))

    def test_term_substitution(self):
        term1 = Terms.FVC("x")
        term2 = Terms.FVC("y")
        var = "x"
        result = term_substitution(term1, term2, var)
        self.assertEqual(result, Terms.FVC("y"))


if __name__ == "__main__":
    unittest.main()
