import unittest
import OneFile
from OneFile import Terms_ind


class TestTermsInd(unittest.TestCase):
    def test_terms_ind(self):
        self.assertIsNotNone(Terms_ind)
        self.assertIsNotNone(OneFile.Terms_ind)


if __name__ == "__main__":
    unittest.main()
