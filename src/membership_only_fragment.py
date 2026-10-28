# Membership-Only Fragment

# This class implements the membership-only fragment of first-order logic.
# It provides a method to check if an element is a member of a set.
# The method adheres to the deduction rules of first-order logic.

# This file contains the implementation of the membership-only fragment.

class MembershipOnlyFragment:
    def __init__(self):
        pass

    def is_member(self, element, set):
        """Check if an element is a member of a set."""
        return element in set
