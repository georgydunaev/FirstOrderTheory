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

    def test_dosubst_and_typing_context(self):
        tau = TImp(TVar(0), TImp(TProp, TVar(1)))
        self.assertEqual(dosubst(idsubst, tau), tau)
        subst = lambda n: TO if n == 0 else TI
        self.assertEqual(dosubst(subst, tau), TImp(TO, TImp(TProp, TI)))

        ctx = addtotctx(idsubst, 0, TProp)
        self.assertEqual(ctx(0), TProp)
        self.assertEqual(ctx(1), TVar(1))

        # Identity combinator \x0:TProp. x0 has type TProp => TProp
        id_term = ELam(0, TProp, EVar(0))
        self.assertEqual(TypeOfTerm(idsubst, id_term), TImp(TProp, TProp))
        # Polymorphic BA instantiated at TO applied to (\x0:TO. TP x0)
        ba_to = ECon(BA, lambda n: TO if n == 0 else TVar(n))
        self.assertEqual(TypeOfTerm(idsubst, ba_to), TImp(TImp(TO, TProp), TProp))
        lam_tp = ELam(0, TO, EApp(ECon(TP), EVar(0)))
        self.assertEqual(TypeOfTerm(idsubst, EApp(ba_to, lam_tp)), TProp)

if __name__ == '__main__':
    unittest.main()