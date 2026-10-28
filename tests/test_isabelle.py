import unittest

class TestIsabelle(unittest.TestCase):
    def test_isabelle_module(self):
        # Test the Isabelle module
        from FirstOrderTheory.Isabelle import Types, TImp, TProp, TO, TI, eqTypes
        from FirstOrderTheory.Isabelle import Types, TImp, TProp, TO, TI, eqTypes

        def test_types_constructors(self):
            # Test TVar constructor
            self.assertEqual(Types.TVar(0), Types.TVar(0))
            # Test TImp constructor
            self.assertEqual(Types.TImp(TProp, TProp), Types.TImp(TProp, TProp))
            # Test TProp constructor
            self.assertEqual(Types.TProp, Types.TProp)
            # Test TO constructor
            self.assertEqual(Types.TO, Types.TO)
            # Test TI constructor
            self.assertEqual(Types.TI, Types.TI)

        def test_eqTypes(self):
            # Test eqTypes with TVar
            self.assertTrue(eqTypes(Types.TVar(0), Types.TVar(0)))
            # Test eqTypes with TImp
            self.assertTrue(eqTypes(Types.TImp(TProp, TProp), Types.TImp(TProp, TProp)))
            # Test eqTypes with TProp
            self.assertTrue(eqTypes(Types.TProp, Types.TProp))
            # Test eqTypes with TO
            self.assertTrue(eqTypes(Types.TO, Types.TO))
            # Test eqTypes with TI
            self.assertTrue(eqTypes(Types.TI, Types.TI))
        from FirstOrderTheory.Isabelle import Types, TImp, TProp, TO, TI, eqTypes
        self.assertTrue(hasattr(Isabelle, 'some_function'))

if __name__ == '__main__':
    unittest.main()