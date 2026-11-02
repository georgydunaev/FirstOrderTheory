import unittest
from examples.logical_derivation_example import P, Q, R, x_values


class TestLogicalDerivationExample(unittest.TestCase):
    def test_predicate_definitions(self):
        self.assertTrue(P(5))
        self.assertTrue(Q(5))
        self.assertTrue(R(4))
        self.assertTrue(P(11))
        self.assertFalse(Q(11))
        self.assertFalse(R(3))

    def test_hypothesis(self):
        self.assertTrue(any(P(x) and Q(x) and R(x) for x in x_values))

    def test_conclusion(self):
        self.assertTrue(any(R(x) for x in x_values))


if __name__ == "__main__":
    unittest.main()
