import unittest

class TestMembershipOnly(unittest.TestCase):
    def test_membership_only(self):
        from OneFileZFC import MembershipOnly

    def test_membership_only(self):
        # Test basic membership
        self.assertTrue(MembershipOnly(1, [1, 2, 3]))
        self.assertFalse(MembershipOnly(4, [1, 2, 3]))

    def test_empty_list(self):
        # Test empty list
        self.assertFalse(MembershipOnly(1, []))

    def test_non_list_input(self):
        # Test non-list input
        with self.assertRaises(TypeError):
            MembershipOnly(1, "not a list")
        self.assertTrue(True)

if __name__ == '__main__':
    unittest.main()