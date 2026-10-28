import sys
sys.path.append('/botworkspace/FirstOrderTheory')

import unittest
from cognition import FVC, FSC, term_substitution

class TestTermSubstitution(unittest.TestCase):
    def test_substitution_FVC(self):
        t1 = FVC('x')
        t2 = FVC('y')
        x = 'x'
        result = term_substitution(t1, t2, x)
        self.assertEqual(result, t2)
    
    def test_substitution_FSC(self):
        t1 = FSC('f', [FVC('x'), FVC('y')])
        t2 = FVC('z')
        x = 'x'
        result = term_substitution(t1, t2, x)
        expected = FSC('f', [t2, FVC('y')])
        self.assertEqual(result, expected)

if __name__ == '__main__':
    unittest.main()