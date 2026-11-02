import os, sys
sys.path.append( os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))
sys.path.append( os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))
import unittest
from FirstOrderTheory import Isabelle
from FirstOrderTheory.Isabelle import Types, TImp, TProp, TO, TI, eqTypes


class TestIsabelle(unittest.TestCase):
    def test_isabelle_module(self):
        self.assertEqual(Types.TVar(0), Types.TVar(0))
        self.assertEqual(Types.TImp(TProp, TProp), Types.TImp(TProp, TProp))
        self.assertEqual(Types.TProp, Types.TProp)
        self.assertEqual(Types.TO, Types.TO)
        self.assertEqual(Types.TI, Types.TI)

        self.assertTrue(eqTypes(Types.TVar(0), Types.TVar(0)))
        self.assertTrue(eqTypes(Types.TImp(TProp, TProp), Types.TImp(TProp, TProp)))
        self.assertTrue(eqTypes(Types.TProp, Types.TProp))
        self.assertTrue(eqTypes(Types.TO, Types.TO))
        self.assertTrue(eqTypes(Types.TI, Types.TI))
        self.assertTrue(hasattr(Isabelle, "some_function"))


if __name__ == "__main__":
    unittest.main()
