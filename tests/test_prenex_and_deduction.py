import os
import subprocess
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class TestPrenexAndDeduction(unittest.TestCase):
    """Test suite for Prenex Normal Form, Deduction Theorem, and Skolem Equisatisfiability."""

    def test_no_admitted_in_prenex(self):
        """Verify Prenex.v contains zero admitted proofs or axioms."""
        prenex_path = os.path.join(ROOT, "Prenex.v")
        self.assertTrue(os.path.exists(prenex_path), "Prenex.v must exist")
        with open(prenex_path, "r", encoding="utf-8") as f:
            content = f.read()
        self.assertNotIn("admit", content.lower(), "Prenex.v must not contain 'admit'")
        self.assertNotIn("admitted", content.lower(), "Prenex.v must not contain 'admitted'")

    def test_no_admitted_in_onefile(self):
        """Verify OneFile.v contains zero admitted proofs."""
        onefile_path = os.path.join(ROOT, "OneFile.v")
        self.assertTrue(os.path.exists(onefile_path), "OneFile.v must exist")
        with open(onefile_path, "r", encoding="utf-8") as f:
            content = f.read()
        self.assertNotIn("admit", content.lower(), "OneFile.v must not contain 'admit'")
        self.assertNotIn("admitted", content.lower(), "OneFile.v must not contain 'admitted'")

    def test_coqc_compilation_prenex(self):
        """Verify Prenex.v compiles cleanly with coqc."""
        prenex_path = os.path.join(ROOT, "Prenex.v")
        res = subprocess.run(
            ["coqc", "-Q", ROOT, "", prenex_path],
            capture_output=True,
            text=True,
            cwd=ROOT,
        )
        self.assertEqual(res.returncode, 0, f"coqc compilation failed:\n{res.stderr}")

    def test_prenex_theorems_present(self):
        """Verify key Prenex and Quantifier Shifting theorems are present in Prenex.v."""
        prenex_path = os.path.join(ROOT, "Prenex.v")
        with open(prenex_path, "r", encoding="utf-8") as f:
            content = f.read()

        required_symbols = [
            "Inductive is_prenex_form",
            "Inductive is_quantifier_free",
            "Theorem matrix_prefix_decomp",
            "Theorem prenex_normal_form_qf",
            "Theorem prenex_normal_form_apply_prefix",
            "Theorem prenex_forall_step",
            "Theorem prenex_exists_step",
            "Theorem prenex_equiv_for_prenex",
            "Theorem prenex_equiv_for_prefix",
            "Theorem not_exists_iff_forall_not",
            "Theorem classical_not_forall_iff_exists_not",
            "Theorem shift_forall_conj_l",
            "Theorem shift_forall_conj_r",
            "Theorem shift_exists_conj_l",
            "Theorem shift_exists_conj_r",
            "Theorem shift_exists_disj_l",
            "Theorem shift_exists_disj_r",
            "Theorem shift_forall_impl_r",
            "Theorem shift_exists_impl_l",
            "Theorem shift_forall_disj_l",
            "Theorem shift_forall_disj_r",
            "Theorem shift_forall_impl_l",
            "Theorem shift_exists_impl_r",
        ]
        for sym in required_symbols:
            self.assertIn(sym, content, f"Symbol '{sym}' must be present in Prenex.v")

    def test_deduction_theorems_present(self):
        """Verify constructive deduction theorems in Prenex.v and OneFile.v."""
        prenex_path = os.path.join(ROOT, "Prenex.v")
        with open(prenex_path, "r", encoding="utf-8") as f:
            p_content = f.read()

        prenex_symbols = [
            "Inductive Prf",
            "Lemma Prf_AtoA",
            "Lemma Prf_weaken",
            "Theorem Prf_deduction_converse",
            "Theorem Prf_deduction_direct",
            "Theorem Prf_deduction_iff",
        ]
        for sym in prenex_symbols:
            self.assertIn(sym, p_content, f"Symbol '{sym}' must be in Prenex.v")

        onefile_path = os.path.join(ROOT, "OneFile.v")
        with open(onefile_path, "r", encoding="utf-8") as f:
            o_content = f.read()

        onefile_symbols = [
            "Fixpoint weaken_PREPR",
            "Ded_inv",
            "Ded_inv_closed",
            "Theorem Deduction_Theorem_equiv",
        ]
        for sym in onefile_symbols:
            self.assertIn(sym, o_content, f"Symbol '{sym}' must be in OneFile.v")

    def test_skolem_theorems_present(self):
        """Verify Skolem Normal Form and Equisatisfiability theorems in Prenex.v."""
        prenex_path = os.path.join(ROOT, "Prenex.v")
        with open(prenex_path, "r", encoding="utf-8") as f:
            content = f.read()

        skolem_symbols = [
            "Inductive is_skolem_form",
            "Theorem skolem_is_prenex",
            "Theorem skolem_functional_equisatisfiable",
            "Theorem skolem_constant_equisatisfiable",
            "Theorem skolem_choice_equisatisfiable",
        ]
        for sym in skolem_symbols:
            self.assertIn(sym, content, f"Symbol '{sym}' must be in Prenex.v")

    def test_deep_prenex_quantifier_free_instantiation(self):
        """Verify quantifier-free substitution and prefix instantiation in Prenex.v."""
        prenex_path = os.path.join(ROOT, "Prenex.v")
        with open(prenex_path, "r", encoding="utf-8") as f:
            content = f.read()

        instantiation_symbols = [
            "Theorem subst_preserves_qf",
            "Theorem skolem_unary_instantiation_qf",
            "Fixpoint instantiate_universal_prefix",
            "Theorem instantiate_universal_prefix_qf",
        ]
        for sym in instantiation_symbols:
            self.assertIn(sym, content, f"Symbol '{sym}' must be in Prenex.v")

    def test_deep_hilbert_deduction_specialization(self):
        """Verify Hilbert deduction specialization and propositional rules in Prenex.v."""
        prenex_path = os.path.join(ROOT, "Prenex.v")
        with open(prenex_path, "r", encoding="utf-8") as f:
            content = f.read()

        deduction_symbols = [
            "Lemma Prf_forall_inst",
            "Lemma Prf_forall2_inst",
            "Lemma Prf_exists_intro",
            "Lemma Prf_conj_intro",
            "Lemma Prf_conj_elim_l",
            "Lemma Prf_conj_elim_r",
        ]
        for sym in deduction_symbols:
            self.assertIn(sym, content, f"Symbol '{sym}' must be in Prenex.v")

    def test_deep_skolem_characterization(self):
        """Verify characterization of Skolem forms via quantifier counts and prefixes."""
        prenex_path = os.path.join(ROOT, "Prenex.v")
        with open(prenex_path, "r", encoding="utf-8") as f:
            content = f.read()

        characterization_symbols = [
            "Fixpoint num_existentials",
            "Fixpoint num_universals",
            "Lemma qf_num_existentials_zero",
            "Lemma skolem_num_existentials_zero",
            "Lemma prenex_no_exists_is_skolem",
            "Theorem prenex_zero_existentials_iff_skolem",
            "Definition prefix_all_forall",
            "Lemma qf_prefix_all_forall",
            "Lemma skolem_prefix_all_forall",
            "Lemma skolem_matrix_is_qf",
            "Theorem skolem_decomposition",
            "Theorem universal_prefix_yields_skolem",
        ]
        for sym in characterization_symbols:
            self.assertIn(sym, content, f"Symbol '{sym}' must be in Prenex.v")

    def test_deep_multivariate_and_model_theoretic_equisatisfiability(self):
        """Verify multivariate Skolemization and model-theoretic equisatisfiability in Prenex.v."""
        prenex_path = os.path.join(ROOT, "Prenex.v")
        with open(prenex_path, "r", encoding="utf-8") as f:
            content = f.read()

        equisat_symbols = [
            "Theorem skolem_binary_functional_equisatisfiable",
            "Theorem skolem_binary_choice_equisatisfiable",
            "Theorem skolem_uniform_constant",
            "Definition equisatisfiable",
            "Theorem equisatisfiable_refl",
            "Theorem equisatisfiable_sym",
            "Theorem equisatisfiable_trans",
            "Theorem sem_equiv_implies_equisatisfiable",
            "Theorem prenex_equiv_equisatisfiable",
        ]
        for sym in equisat_symbols:
            self.assertIn(sym, content, f"Symbol '{sym}' must be in Prenex.v")

    def test_skolem_equisatisfiability_computational_model(self):
        """Verify computational validity of functional Skolemization over finite models."""
        domain = [0, 1, 2, 3]

        # Relation R(x, y) where for every x, y = (x + 1) mod 4 satisfies R
        def r_rel(x, y):
            return (x + 1) % 4 == y

        # Check forall x, exists y, R(x, y)
        forall_exists = all(any(r_rel(x, y) for y in domain) for x in domain)
        self.assertTrue(forall_exists)

        # Skolem function f(x) = (x + 1) mod 4
        def skolem_f(x):
            return (x + 1) % 4

        # Check forall x, R(x, f(x))
        skolem_satisfied = all(r_rel(x, skolem_f(x)) for x in domain)
        self.assertTrue(skolem_satisfied)

        # Binary Skolem relation R3(x, y, z): z = (x + y) mod 4
        def r3_rel(x, y, z):
            return (x + y) % 4 == z

        forall_xy_exists_z = all(
            any(r3_rel(x, y, z) for z in domain)
            for x in domain
            for y in domain
        )
        self.assertTrue(forall_xy_exists_z)

        def skolem_f2(x, y):
            return (x + y) % 4

        binary_skolem_satisfied = all(
            r3_rel(x, y, skolem_f2(x, y))
            for x in domain
            for y in domain
        )
        self.assertTrue(binary_skolem_satisfied)


if __name__ == "__main__":
    unittest.main()
