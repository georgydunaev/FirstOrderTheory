import unittest
from src.membership_only_fragment import MembershipOnlyFragment

class TestMembershipOnlyFragment(unittest.TestCase):
    def setUp(self):
        self.fragment = MembershipOnlyFragment()

    def test_element_in_set(self):
        self.assertTrue(self.fragment.is_member(1, {1, 2, 3}))

    def test_element_not_in_set(self):
        self.assertFalse(self.fragment.is_member(4, {1, 2, 3}))

    def test_empty_set(self):
        self.assertFalse(self.fragment.is_member(1, set()))

    def test_empty_element(self):
        self.assertFalse(self.fragment.is_member('', {'a', 'b', 'c'}))

    def test_set_with_multiple_elements(self):
        self.assertTrue(self.fragment.is_member('a', {'a', 'b', 'c'}))
        self.assertFalse(self.fragment.is_member('d', {'a', 'b', 'c'}))

    def test_set_with_duplicate_elements(self):
        self.assertTrue(self.fragment.is_member(1, {1, 1, 2, 3}))
        self.assertFalse(self.fragment.is_member(4, {1, 1, 2, 3}))

    def test_non_hashable_elements(self):
        with self.assertRaises(TypeError):
            self.fragment.is_member([1, 2], {[1, 2], [3, 4]})

if __name__ == '__main__':
    unittest.main()