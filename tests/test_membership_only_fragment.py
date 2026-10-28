# Unit Tests for Membership-Only Fragment

import sys
import os
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
from src.membership_only_fragment import MembershipOnlyFragment

import unittest
from FirstOrderTheory.src.membership_only_fragment import MembershipOnlyFragment

class TestMembershipOnlyFragment(unittest.TestCase):
    def setUp(self):
        self.fragment = MembershipOnlyFragment()

    def test_is_member(self):
        # Test with empty set
        self.assertFalse(self.fragment.is_member(1, set()))
        
        # Test with non-empty set
        test_set = {1, 2, 3}
        self.assertTrue(self.fragment.is_member(1, test_set))
        self.assertFalse(self.fragment.is_member(4, test_set))

if __name__ == '__main__':
    unittest.main()
