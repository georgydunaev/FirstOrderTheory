import unittest
from utils import read, strip_comments

class TestUtils(unittest.TestCase):
    def test_read(self):
        # Test reading a file
        content = read('tests/test_utils.py')
        self.assertIsInstance(content, str)

    def test_strip_comments(self):
        # Test stripping comments from Coq code
        coq_code = "(* This is a comment *) This is not a comment"
        stripped_code, depth, min_depth = strip_comments(coq_code)
        self.assertEqual(stripped_code, "                  This is not a comment")
        self.assertEqual(depth, 0)
        self.assertEqual(min_depth, 0)

if __name__ == '__main__':
    unittest.main()