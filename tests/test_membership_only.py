import unittest
from OneFileZFC import MembershipOnly


class TestMembershipOnly(unittest.TestCase):
    def test_membership_only(self):
        self.assertTrue(MembershipOnly(1, [1, 2, 3]))
        self.assertFalse(MembershipOnly(4, [1, 2, 3]))

    def test_empty_list(self):
        self.assertFalse(MembershipOnly(1, []))

    def test_non_list_input(self):
        with self.assertRaises(TypeError):
            MembershipOnly(1, "not a list")


if __name__ == "__main__":
    unittest.main()
