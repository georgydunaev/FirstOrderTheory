import unittest
from src.formalized_theorems import *

class TestFormalizedTheorems(unittest.TestCase):
    def test_types_definition(self):
        # Test the inductive definition of types
        self.assertTrue(Types(TVar(0)))
        self.assertTrue(Types(TImp(TProp, TProp)))
        self.assertTrue(Types(TProp))
        self.assertTrue(Types(TO))
        self.assertTrue(Types(TI))

    def test_eqTypes(self):
        # Test the fixpoint for equality of types
        self.assertTrue(eqTypes(TVar(0), TVar(0)))
        self.assertTrue(eqTypes(TImp(TProp, TProp), TImp(TProp, TProp)))
        self.assertTrue(eqTypes(TProp, TProp))
        self.assertTrue(eqTypes(TO, TO))
        self.assertTrue(eqTypes(TI, TI))
        self.assertFalse(eqTypes(TVar(0), TVar(1)))

    def test_PT_definition(self):
        # Test the inductive definition of primitive terms
        self.assertTrue(PT(LRA))
        self.assertTrue(PT(BA))
        self.assertTrue(PT(TP))
        self.assertTrue(PT(Impl))
        self.assertTrue(PT(Fora))
        self.assertTrue(PT(EFalse))
        self.assertTrue(PT(Econj))
        self.assertTrue(PT(Edisj))
        self.assertTrue(PT(Eimp))

    def test_PTT(self):
        # Test the fixpoint for the type of primitive terms
        self.assertEqual(PTT(LRA), TImp(TProp, TImp(TProp, TProp)))
        self.assertEqual(PTT(BA), TImp(TImp(TVar(0), TProp), TProp))
        self.assertEqual(PTT(TP), TImp(TO, TProp))
        self.assertEqual(PTT(Impl), TImp(TO, TImp(TO, TO)))
        self.assertEqual(PTT(Fora), TImp(TImp(TI, TO), TO))
        self.assertEqual(PTT(EFalse), TO)
        self.assertEqual(PTT(Econj), TImp(TO, TImp(TO, TO)))
        self.assertEqual(PTT(Edisj), TImp(TO, TImp(TO, TO)))
        self.assertEqual(PTT(Eimp), TImp(TO, TImp(TO, TO)))

if __name__ == '__main__':
    unittest.main()