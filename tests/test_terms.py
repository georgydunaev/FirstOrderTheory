import unittest
from FirstOrderTheory.cognition import FVC, FSC, term_substitution

class TestTerms(unittest.TestCase):
    def test_term_substitution(self):
        # Test substitution in FVC constructor
        t1 = FVC('x')
        t2 = FVC('y')
        x = 'x'
        result = term_substitution(t1, t2, x)
        self.assertEqual(result, t2)

        # Test substitution in FSC constructor
        t1 = FSC('f', [FVC('x')])
        t2 = FVC('y')
        x = 'x'
        result = term_substitution(t1, t2, x)
        self.assertEqual(result, FSC('f', [t2]))

if __name__ == '__main__':
    unittest.main()