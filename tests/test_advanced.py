import os, sys
sys.path.append( os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))
sys.path.append( os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))
import sys
import unittest

sys.path.append("/botworkspace/FirstOrderTheory")
from FirstOrderTheory import Terms_ind


class FVC:
    def __init__(self, var):
        self.var = var

    def __eq__(self, other):
        return isinstance(other, FVC) and self.var == other.var


class FSC:
    def __init__(self, func, args):
        self.func = func
        self.args = args

    def __eq__(self, other):
        return isinstance(other, FSC) and self.func == other.func and self.args == other.args


class TestAdvanced(unittest.TestCase):
    def test_terms_ind(self):
        sv = "x"
        self.assertTrue(Terms_ind(lambda t: t == FVC(sv), lambda sv: True, lambda f, v: True, FVC(sv)))

        f = "f"
        v = [FVC("x"), FVC("y")]
        self.assertTrue(
            Terms_ind(
                lambda t: t == FSC(f, v),
                lambda sv: True,
                lambda f, v: all(
                    Terms_ind(lambda t: t == term, lambda sv: True, lambda f, v: True, term) for term in v
                ),
                FSC(f, v),
            )
        )

        f1 = "f1"
        f2 = "f2"
        v1 = [FVC("x"), FVC("y")]
        v2 = [FSC(f1, v1), FVC("z")]
        self.assertTrue(
            Terms_ind(
                lambda t: t == FSC(f2, v2),
                lambda sv: True,
                lambda f, v: all(
                    Terms_ind(lambda t: t == term, lambda sv: True, lambda f, v: True, term) for term in v
                ),
                FSC(f2, v2),
            )
        )


if __name__ == "__main__":
    unittest.main()
